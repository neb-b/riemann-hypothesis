module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0323
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0312
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0313

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfBComponentsMemCompletedLatticeOffConj
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfBComp
open GlobalTheory.AdForm.HalfPairing GlobalTheory.LatVac

theorem comp_mem {D : D7} {S T : HSp D} {N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hc : D.host.ccK = ⊤) (hN : IsSelfDualC S N) {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)}
    (he : Formalism.L2.NTheta.IsIdemAt e P) (h0 : infPart D e = 0) {x : Formalism.L2.Col.HomE D.host.E S.rank T.rank}
    (hx : x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N')) :
    ((LinearMap.toMatrix' x).map fun r => e * incA D r : WO S T) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  obtain ⟨s, hs, hsx⟩ := hx
  have hs' : s ∉ P.asIdeal := hs
  have hne : s ≠ 0 := fun h => hs' (h ▸ zero_mem _)
  have hs0 : (s : D.host.E) ≠ 0 := fun h => hne (RingOfIntegers.ext h)
  have h1 : finPart D (e * incA D ((s : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra h
    exact hs' ((he.2 _ hne).2 h)
  have h4 := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ h1 _
    (finTens_mem_latO (one_mem_intAf _) (toMatrix_mem_latRat hc hN hsx))
  convert h4 using 1
  ext i j
  rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  refine GlobalTheory.SplitScalar.adele_ext (by simp only [RingHom.map_mul, h0, zero_mul]) ?_
  have h6 : finPart D (finTens 1 (LinearMap.toMatrix' (s • x)) i j) =
      finPart D (incA D ((s : D.host.E) * LinearMap.toMatrix' x i j)) := rfl
  rw [RingHom.map_mul (finPart D) (_ * _), h6, ← RingHom.map_mul, mul_assoc, ← RingHom.map_mul (incA D),
    inv_mul_cancel_left₀ hs0]

theorem halfB_mem_locP {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}
    {SS : Finset (HeightOneSpectrum (𝓞 E))} {M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)} {c : ℕ} (hc : 0 < c)
    {y : Formalism.L2.Col.HomE E a b} (hy : y ∈ halfBO SS M c) {P : HeightOneSpectrum (𝓞 E)} (hP : P ∈ SS) :
    y ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M := by
  have h : ((c : E) ^ expS SS P)⁻¹ • y ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M := (Submodule.mem_iInf _).1 hy P
  have he : expS SS P = 1 := by
    unfold expS; rw [if_pos hP]
  have hc' : (c : E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  rw [he, zpow_one] at h
  have := nsmul_mem h c
  rwa [← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hc', one_smul] at this


set_option maxHeartbeats 1000000 in
theorem ybmem : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ y' ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, (GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' y')) - ((LinearMap.toMatrix' y').map fun r => cA D e * incA D r) ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True) := by
  intro D ψ θ S T δ sc hP e SS hE h2 N N' hN hN' c hc hcQ x' hx
  have hc0 : (c : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have hA : ((LinearMap.toMatrix' x').map fun r => e * incA D r : WO S T) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True := by
    obtain ⟨⟨es, hes, rfl⟩, -⟩ := hE
    have e1 : ((LinearMap.toMatrix' x').map fun r => (∑ PP ∈ SS, es PP) * incA D r : WO S T) =
        ∑ PP ∈ SS, ((LinearMap.toMatrix' x').map fun r => (es PP) * incA D r : WO S T) := by
      ext i j
      rw [Matrix.map_apply, Matrix.sum_apply, Finset.sum_mul]
      rfl
    rw [e1]
    refine sum_mem fun PP hPP => comp_mem hP.cc hN (hes PP hPP) ?_ (halfB_mem_locP hc hx hPP)
    exact GlobalTheory.PlaceVec.idemSum_infPart (P := {PP}) ⟨⟨es, fun Q hQ => by
      rw [Finset.mem_singleton.1 hQ]; exact hes PP hPP, (Finset.sum_singleton _ _).symm⟩, (hes PP hPP).1.2.1⟩
  have hcx : ((c : D.host.E) • x') ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' :=
    GlobalTheory.ThetaMove.mem_of_locP fun Q => smul_mem_locP hc hx Q
  have hloc : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), ¬ (Q ∈ SS ∨ Formalism.L2.Col.conjPrime₂ Q ∈ SS) →
      x' ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := by
    intro Q hQ
    have h : ((c : D.host.E) ^ expS SS Q)⁻¹ • x' ∈
        Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') :=
      (Submodule.mem_iInf _).1 hx Q
    have he : expS SS Q = 0 := by
      unfold expS; rw [if_neg fun h => hQ (Or.inl h), if_neg fun h => hQ (Or.inr h)]
    rwa [he, zpow_zero, _root_.inv_one, one_smul] at h
  obtain ⟨d, hd0, hdx, hdQ⟩ := _root_.GlobalTheory.OffDen.exists_den_avoid D.host.E S.rank T.rank _
    (fun Q => Q ∈ SS ∨ Formalism.L2.Col.conjPrime₂ Q ∈ SS) c hc x' hcx hloc
  obtain ⟨a₁, a₂, ha₁, ha₂, ho⟩ := _root_.GlobalTheory.OffIdemTwo.off_two D e SS hE c hc d hd0 hdQ
  have hB : a₁ • GlobalTheory.LatVac.finTens 1 (LinearMap.toMatrix' ((c : D.host.E) • x')) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True :=
    GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ ha₁ _
      (GlobalTheory.LatVac.finTens_mem_latO (GlobalTheory.LatVac.one_mem_intAf _) (toMatrix_mem_latRat hP.cc hN hcx))
  have hC : a₂ • GlobalTheory.LatVac.finTens 1 (LinearMap.toMatrix' ((d : D.host.E) • x')) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True :=
    GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ ha₂ _
      (GlobalTheory.LatVac.finTens_mem_latO (GlobalTheory.LatVac.one_mem_intAf _) (toMatrix_mem_latRat hP.cc hN hdx))
  convert add_mem hA (add_mem hB hC) using 1
  have hinf := GlobalTheory.PlaceVec.idemSum_infPart hE
  have hinfc := GlobalTheory.PlaceVec.infPart_cA hinf
  have i1 : ∀ (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) i j,
      infPart D (GlobalTheory.VacUnique.finRat S T M i j) = 0 := fun M i j => by
    have := congrFun (congrFun (GlobalTheory.VacUnique.finRat_inf S T M) i) j
    simpa using this
  have f1 : ∀ (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) i j,
      finPart D (GlobalTheory.VacUnique.finRat S T M i j) = finPart D (incA D (M i j)) := fun M i j => by
    rw [GlobalTheory.LatVacSign.finRat_eq]; rfl
  rw [← GlobalTheory.LatVacSign.finRat_eq, ← GlobalTheory.LatVacSign.finRat_eq]
  ext i j
  rw [Matrix.sub_apply, Matrix.add_apply, Matrix.add_apply, Matrix.map_apply, Matrix.map_apply, Matrix.smul_apply,
    Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
  refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
  · rw [RingHom.map_sub, RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_mul, RingHom.map_mul,
      RingHom.map_mul, i1, i1, i1, hinf, hinfc]
    simp only [mul_zero, zero_mul, sub_zero, add_zero]
  · have hs : ∀ r : D.host.E, LinearMap.toMatrix' (r • x') i j = r * LinearMap.toMatrix' x' i j := fun r => by
      rw [map_smul]; rfl
    have ho' := congrArg (finPart D) ho
    rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_one, RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_mul] at ho'
    rw [RingHom.map_sub, RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_mul, RingHom.map_mul,
      RingHom.map_mul, f1, f1, f1, hs, hs, RingHom.map_mul (incA D), RingHom.map_mul (incA D), RingHom.map_mul (finPart D),
      RingHom.map_mul (finPart D)]
    linear_combination (finPart D (incA D (LinearMap.toMatrix' x' i j))) * ho'

end GlobalTheory.HalfBComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.DisjComb

open GlobalTheory.FinPl.LatMem

variable {D : D7}

theorem mul_eq_zero_of_disj {P P' : Pl D → Prop} (hd : ∀ p, P p → ¬ P' p) {a b : AE D} (ha : a ∈ idAt D P)
    (hb : b ∈ idAt D P') : a * b = 0 := by
  obtain ⟨ha0, haw⟩ := mem_idAt_iff.1 ha
  obtain ⟨hb0, hbw⟩ := mem_idAt_iff.1 hb
  refine GlobalTheory.AdelicU.Supp.adTens_ext (fun w => ?_) fun v => ?_
  · rw [map_mul, compInf_eq_zero ha0, zero_mul, map_zero]
  · rw [map_mul, map_zero, compFin_eq_compAt, compFin_eq_compAt]
    by_cases hv : P v
    · rw [hbw v (hd v hv), mul_zero]
    · rw [haw v hv, zero_mul]

theorem mul_eq_zero_of_off {P : Pl D → Prop} {a b : AE D} (ha : a ∈ idOff D P) (hb : b ∈ idAt D P) : a * b = 0 := by
  obtain ⟨hb0, hbw⟩ := mem_idAt_iff.1 hb
  have haw : ∀ v, P v → compAt D v a = 0 := by
    intro v hv
    unfold idOff at ha
    rw [Submodule.mem_iInf] at ha
    exact RingHom.mem_ker.1 (ha ⟨v, hv⟩)
  refine GlobalTheory.AdelicU.Supp.adTens_ext (fun w => ?_) fun v => ?_
  · rw [map_mul, compInf_eq_zero hb0, mul_zero, map_zero]
  · rw [map_mul, map_zero, compFin_eq_compAt, compFin_eq_compAt]
    by_cases hv : P v
    · rw [haw v hv, zero_mul]
    · rw [hbw v hv, mul_zero]

def idem (P : Pl D → Prop) : AE D := pairA D.host.F 0 (indP D.host.F P) ⊗ₜ[D.host.F] (1 : D.host.E)

theorem idem_mem (P : Pl D → Prop) : idem P ∈ idAt D P := tmul_mem_idAt (indicatorAdele_supported D.host.F P) 1

theorem cA_idem (P : Pl D → Prop) : cA D (idem P) = idem P := by
  show pairA D.host.F 0 (indP D.host.F P) ⊗ₜ[D.host.F] star (1 : D.host.E) = _
  rw [star_one]; rfl

theorem idem_mul {P : Pl D → Prop} {a : AE D} (ha : a ∈ idAt D P) : idem P * a = a := by
  rw [mul_comm]; exact mul_indP ha

theorem symplO_disj {S T : HSp D} {P P' : Pl D → Prop} (hd : ∀ p, P p → ¬ P' p) {x y : WO S T} (hx : MxAt P x)
    (hy : MxAt P' y) : symplO S T x y = 0 := by
  refine GlobalTheory.SplitScalar.symplO_eq_zero S T (a := idem P) (b := idem P') ?_ (fun i j => idem_mul (hx i j))
    (fun i j => idem_mul (hy i j))
  rw [cA_idem]
  exact mul_eq_zero_of_disj hd (idem_mem P) (idem_mem P')

theorem mxAt_mono {P Q : Pl D → Prop} (h : ∀ p, P p → Q p) {m n : ℕ} {x : Mx D m n} (hx : MxAt P x) : MxAt Q x := by
  intro i j
  obtain ⟨h0, hw⟩ := mem_idAt_iff.1 (hx i j)
  exact mem_idAt_iff.2 ⟨h0, fun w hw' => hw w fun hp => hw' (h w hp)⟩

theorem comb_single (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (f : WO S T → ℂ) :
    comb ψ S T (Finsupp.single w 1) f = heisO ψ S T w f := by
  unfold comb
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul]

theorem mem_congGrp' {V : HSp D} {I : Ideal (AE D)} {g : GA D V} (hg : g ∈ congGrp V I) :
    ∀ i j, mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j ∈ I := by
  unfold congGrp at hg
  rw [MonoidHom.mem_ker] at hg
  intro i j
  have := congrArg (fun x : GL (Fin V.rank) (AE D ⧸ I) => x.1 i j) hg
  rw [← Ideal.Quotient.eq]
  simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
  exact this

theorem actO_off {S T : HSp D} {P : Pl D → Prop} {g : GA D S} {h : GA D T} (hg : g ∈ grpOff S P)
    (hh : h ∈ grpOff T P) {u : WO S T} (hu : MxAt P u) : actO S T g h u = u := by
  have hg' := mem_congGrp' (inv_mem hg)
  have hh' := mem_congGrp' hh
  have h1 : HMul.hMul (mt T h - 1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = 0 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.zero_apply]
    exact Finset.sum_eq_zero fun k _ => mul_eq_zero_of_off (by simpa using hh' i k) (hu k j)
  have h2 : HMul.hMul (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S g⁻¹ - 1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) = 0 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.zero_apply]
    exact Finset.sum_eq_zero fun k _ => by
      rw [mul_comm]; exact mul_eq_zero_of_off (by simpa using hg' k j) (hu i k)
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h2
  unfold actO
  rw [h1]
  exact h2

end GlobalTheory.DisjComb

namespace GlobalTheory.DisjComb

open GlobalTheory.FinPl.LatMem

variable {D : D7}

theorem compAt_idem {P : Pl D → Prop} {w : Pl D} (hpw : P w) : compAt D w (idem P) = 1 := by
  rw [← compFin_eq_compAt]
  show evalV D.host.F w (indP D.host.F P) ⊗ₜ[D.host.F] (1 : D.host.E) = 1
  rw [evalV_indP, if_pos hpw]
  rfl

theorem sub_idem_mem {P P' : Pl D → Prop} {a : AE D} (ha : a ∈ idAt D (fun p => P p ∨ P' p)) :
    a - idem P * a ∈ idAt D P' := by
  obtain ⟨h0, hw⟩ := mem_idAt_iff.1 ha
  refine mem_idAt_iff.2 ⟨by rw [RingHom.map_sub, RingHom.map_mul, h0, mul_zero, sub_zero], fun w hw' => ?_⟩
  by_cases hpw : P w
  · rw [RingHom.map_sub, RingHom.map_mul, compAt_idem hpw, one_mul, sub_self]
  · rw [RingHom.map_sub, RingHom.map_mul, hw w (fun h => h.elim hpw hw'), mul_zero, sub_zero]


set_option maxHeartbeats 1000000 in
theorem split_latO (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {LS : Lat S} {LT : Lat T}
    (hLS : IsSelfDualC S LS) (hLT : IsSelfDualC T LT) {P P' : Pl D → Prop} (hd : ∀ p, P p → ¬ P' p) {u : WO S T}
    (hu : u ∈ latO S T (LS : Set _) (LT : Set _) (fun p => P p ∨ P' p)) :
    MxAt P (idem P • u) ∧ MxAt P' (u - idem P • u) ∧ idem P • u ∈ latO S T (LS : Set _) (LT : Set _) P ∧
      u - idem P • u ∈ latO S T (LS : Set _) (LT : Set _) P' := by
  have ann := GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ S T LS LT hLS hLT
  have hmono : ∀ (Q Q' : Pl D → Prop), (∀ p, Q p → Q' p) →
      latO S T (LS : Set _) (LT : Set _) Q ≤ latO S T (LS : Set _) (LT : Set _) Q' := by
    intro Q Q' hQ
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, hv, rest⟩
    exact ⟨α, hα, fun v hv' => hv v fun hq => hv' (hQ v hq), rest⟩
  have huM := latO_mxAt hu
  have hu1 : MxAt P (idem P • u) := fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (idem_mem P)
  have hu2 : MxAt P' (u - idem P • u) := fun i j => by
    rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    exact sub_idem_mem (huM i j)
  refine ⟨hu1, hu2, (ann P _ hu1).2 fun u' hu' => ?_, (ann P' _ hu2).2 fun u' hu' => ?_⟩
  · have hsub : symplO S T (idem P • u) u' = symplO S T u u' - symplO S T (u - idem P • u) u' := by
      rw [← GlobalTheory.SplitScalar.symplO_sub_left, sub_sub_cancel]
    rw [hsub, symplO_disj (fun p hp' hp => hd p hp hp') hu2 (latO_mxAt hu'), sub_zero]
    exact (ann _ u huM).1 hu u' (hmono _ _ (fun p hp => Or.inl hp) hu')
  · rw [GlobalTheory.SplitScalar.symplO_sub_left, symplO_disj hd hu1 (latO_mxAt hu'), sub_zero]
    exact (ann _ u huM).1 hu u' (hmono _ _ (fun p hp => Or.inr hp) hu')

theorem isHalf_parts {S T : HSp D} {P : Pl D → Prop} {e : AE D} {u : WO S T} (h : IsHalf e u) :
    IsHalf e (idem P • u) ∧ IsHalf e (u - idem P • u) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · simp only [Matrix.smul_apply, smul_eq_mul]
    rw [mul_left_comm, h i j]
  · simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    rw [mul_sub, h i j, mul_left_comm, h i j]

end GlobalTheory.DisjComb

namespace GlobalTheory.DisjComb

open GlobalTheory.FinPl.LatMem

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (P P' : Pl D → Prop), (∀ p, P p → ¬ P' p) → (∀ e e' : WO S T →₀ ℂ, CombAt P e → CombAt P' e' → ∀ f, comb ψ S T e (comb ψ S T e' f) = comb ψ S T e' (comb ψ S T e f)) ∧ (∀ e : WO S T →₀ ℂ, CombAt P e → IsFinComb e ∧ ∀ LS LT f, Vac ψ S T LS LT P' f → Vac ψ S T LS LT P' (comb ψ S T e f)) ∧ (∀ χS χT (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ e : WO S T →₀ ℂ, CombAt P e → ∀ g ∈ grpOff S P, ∀ h ∈ grpOff T P, ∀ f, IsThetaFunO ψ S T f → om (g, h) (comb ψ S T e f) = comb ψ S T e (om (g, h) f)) ∧ (∀ e e' : WO S T →₀ ℂ, CombAt (fun p => P p ∨ P' p) e → CombAt (fun p => P p ∨ P' p) e' → ∃ e'', CombAt (fun p => P p ∨ P' p) e'' ∧ ∀ f, comb ψ S T e'' f = comb ψ S T e (comb ψ S T e' f)) ∧ ∀ LS LT f, IsSelfDualC S LS → IsSelfDualC T LT → (Vac ψ S T LS LT (fun p => P p ∨ P' p) f ↔ Vac ψ S T LS LT P f ∧ Vac ψ S T LS LT P' f) := by
  intro D ψ hψ S T P P' hd
  have HC := GlobalTheory.HeisComb.main D ψ S T
  have hcomm : ∀ (e : WO S T →₀ ℂ), CombAt P e → ∀ w : WO S T, MxAt P' w → ∀ f,
      heisO ψ S T w (comb ψ S T e f) = comb ψ S T e (heisO ψ S T w f) := by
    intro e he w hw f
    have h := HC.2.1 e (Finsupp.single w 1) (fun x hx y hy => by
      rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hy
      subst hy
      exact symplO_disj hd (he x hx) hw) f
    simp only [comb_single] at h
    exact h.symm
  have hmono : ∀ (LS : Lat S) (LT : Lat T) (Q Q' : Pl D → Prop), (∀ p, Q p → Q' p) →
      latO S T (LS : Set _) (LT : Set _) Q ≤ latO S T (LS : Set _) (LT : Set _) Q' := by
    intro LS LT Q Q' hQ
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, hv, rest⟩
    exact ⟨α, hα, fun v hv' => hv v fun hq => hv' (hQ v hq), rest⟩
  have hnsmul : ∀ (Q : Pl D → Prop) (x : WO S T), MxAt Q x → MxAt Q ((2 : ℕ) • x) := by
    intro Q x hx i j
    rw [Matrix.smul_apply]
    exact nsmul_mem (hx i j) 2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e e' he he' f
    exact HC.2.1 e e' (fun x hx y hy => symplO_disj hd (he x hx) (he' y hy)) f
  · intro e he
    have hfin : IsFinComb e := fun u hu => Matrix.ext fun i j => (mem_idAt_iff.1 (he u hu i j)).1
    refine ⟨hfin, fun LS LT f hf => ⟨HC.2.2.1 e f hf.1 hfin hψ, fun u hu => ?_, fun e' he' u hu hh => ?_⟩⟩
    · rw [hcomm e he _ (hnsmul P' u (latO_mxAt hu)), hf.2.1 u hu]
    · rw [hcomm e he u (latO_mxAt hu), hf.2.2 e' he' u hu hh]
  · intro χS χT om hom e he g hg h hh f hf
    unfold comb
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [map_smul, hom.om_heis g h u f hf, actO_off hg hh (he u hu)]
  · intro e e' he he'
    obtain ⟨c'', hsupp, heq⟩ := HC.1 e e'
    refine ⟨c'', fun w hw => ?_, heq⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := hsupp w hw
    intro i j
    rw [Matrix.add_apply]
    exact Ideal.add_mem _ (he x hx i j) (he' y hy i j)
  · intro LS LT f hLS hLT
    constructor
    · intro hf
      refine ⟨⟨hf.1, fun u hu => hf.2.1 u (hmono LS LT _ _ (fun p hp => Or.inl hp) hu),
        fun e he u hu hh => hf.2.2 e he u (hmono LS LT _ _ (fun p hp => Or.inl hp) hu) hh⟩,
        ⟨hf.1, fun u hu => hf.2.1 u (hmono LS LT _ _ (fun p hp => Or.inr hp) hu),
        fun e he u hu hh => hf.2.2 e he u (hmono LS LT _ _ (fun p hp => Or.inr hp) hu) hh⟩⟩
    · rintro ⟨hP, hP'⟩
      refine ⟨hP.1, fun u hu => ?_, fun e he u hu hh => ?_⟩
      · obtain ⟨hm1, hm2, hl1, hl2⟩ := split_latO ψ hψ hLS hLT hd hu
        have hsum : u = idem P • u + (u - idem P • u) := (add_sub_cancel _ _).symm
        rw [hsum, nsmul_add, GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T (symplO_disj hd (hnsmul P _ hm1) (hnsmul P' _ hm2)),
          hP'.2.1 _ hl2, hP.2.1 _ hl1]
      · obtain ⟨hm1, hm2, hl1, hl2⟩ := split_latO ψ hψ hLS hLT hd hu
        obtain ⟨h1, h2⟩ := isHalf_parts (P := P) hh
        have hsum : u = idem P • u + (u - idem P • u) := (add_sub_cancel _ _).symm
        rw [hsum, GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T (symplO_disj hd hm1 hm2), hP'.2.2 e he _ hl2 h2,
          hP.2.2 e he _ hl1 h1]

end GlobalTheory.DisjComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationTwoVariableModelAndLineExte
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod

noncomputable section
namespace GlobalTheory.BiComb

variable {D : D7}

theorem heisO_resS_slice (ψ : AddChar (AF D.host.F) ℂ) {V A L S : HSp D} (o : OrthDec V A L) (F : WO V S → ℂ)
    (w u : WO A S) (v : WO L S) :
    heisO ψ V S ((o.resS S).symm (w, 0)) F ((o.resS S).symm (u, v)) =
      heisO ψ A S w (fun u' => F ((o.resS S).symm (u', v))) u := by
  simp only [heisO]
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero,
    ← map_add, Prod.mk_add_mk, add_zero]

theorem heisO_resT_slice (ψ : AddChar (AF D.host.F) ℂ) {V A L S : HSp D} (o : OrthDec V A L) (F : WO S V → ℂ)
    (w u : WO S A) (v : WO S L) :
    heisO ψ S V ((o.resT S).symm (w, 0)) F ((o.resT S).symm (u, v)) =
      heisO ψ S A w (fun u' => F ((o.resT S).symm (u', v))) u := by
  simp only [heisO]
  rw [o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero,
    ← map_add, Prod.mk_add_mk, add_zero]

theorem comb_resS_slice (ψ : AddChar (AF D.host.F) ℂ) {V A L S : HSp D} (o : OrthDec V A L) (c : WO A S →₀ ℂ)
    (F : WO V S → ℂ) (u : WO A S) (v : WO L S) :
    comb ψ V S (c.mapDomain fun w => (o.resS S).symm (w, 0)) F ((o.resS S).symm (u, v)) =
      comb ψ A S c (fun u' => F ((o.resS S).symm (u', v))) u := by
  classical
  have hinj : Function.Injective fun w : WO A S => (o.resS S).symm (w, 0) := fun a b h => by
    have := congrArg (o.resS S) h
    simp only [AddEquiv.apply_symm_apply, Prod.mk.injEq, and_true] at this
    exact this
  simp only [comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finsupp.mapDomain_support_of_injective hinj, Finset.sum_image (fun a _ b _ h => hinj h)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finsupp.mapDomain_apply_of_injective hinj, heisO_resS_slice]

theorem comb_resT_slice (ψ : AddChar (AF D.host.F) ℂ) {V A L S : HSp D} (o : OrthDec V A L) (c : WO S A →₀ ℂ)
    (F : WO S V → ℂ) (u : WO S A) (v : WO S L) :
    comb ψ S V (c.mapDomain fun w => (o.resT S).symm (w, 0)) F ((o.resT S).symm (u, v)) =
      comb ψ S A c (fun u' => F ((o.resT S).symm (u', v))) u := by
  classical
  have hinj : Function.Injective fun w : WO S A => (o.resT S).symm (w, 0) := fun a b h => by
    have := congrArg (o.resT S) h
    simp only [AddEquiv.apply_symm_apply, Prod.mk.injEq, and_true] at this
    exact this
  simp only [comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finsupp.mapDomain_support_of_injective hinj, Finset.sum_image (fun a _ b _ h => hinj h)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finsupp.mapDomain_apply_of_injective hinj, heisO_resT_slice]

section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_isOne (Y Y' : Type) [Fintype Y] [Fintype Y'] : ∃ Φ : SB (Matrix Y Y' k), IsOne Φ := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hc : IsCompact {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} := GlobalTheory.SplitFlip.isCompact_intMatrix
  exact ⟨⟨_, GlobalTheory.LocFlat.CFac.Span.indicator_one_mem_SB hc ⟨hc.isClosed, GlobalTheory.SplitFlip.isOpen_intMatrix⟩⟩, rfl⟩

end Loc

theorem source_slice_model : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ T₀, p.IsModel ψ F₀ FS T₀ → ∀ (a : (n → k) → ℂ), a ∈ SB _ → ∀ v : WO B.L S, ∃ T₁, p.IsModel ψ FA FS T₁ ∧ ∀ (Ξ : SB (Matrix n n' k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), (∀ x, Ψ.1 x = Ξ.1 x.toCols₁ * a fun r => x r (Sum.inr ())) → ∀ u, T₀ Ψ ((B.o.resS S).symm (u, v)) = T₁ Ξ u := _root_.GlobalTheory.SliceModel.exists_isModel_slice

theorem target_slice_model : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ T₀, p.IsModel ψ FS F₀ T₀ → ∀ (a : (n → k) → ℂ), a ∈ SB _ → ∀ v : WO S B.L, ∃ T₁, p.IsModel ψ FS FA T₁ ∧ ∀ (Ξ : SB (Matrix n' n k)) (Ψ : SB (Matrix (n' ⊕ Unit) n k)), (∀ x, Ψ.1 x = Ξ.1 x.toRows₁ * a (x (Sum.inr ()))) → ∀ u, T₀ Ψ ((B.o.resT S).symm (u, v)) = T₁ Ξ u := _root_.GlobalTheory.SliceModelT.main

theorem comb_bimodel_and_line : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''], (∀ (A S A' : HSp D) (FA : Frame k A.rank n') (FS : Frame k S.rank n) (FA' : Frame k A'.rank n'') Λ c c' (Ξ₁ O₁ : SB (Matrix n n' k)) (Ξ₂ O₂ : SB (Matrix n'' n k)) (Ξ O : SB (Matrix n n' k × Matrix n'' n k)), p.IsBiModel ψ FA FS FA' Λ → p.IsCombAt ψ FA FS c Ξ₁.1 → p.IsCombAt ψ FS FA' c' Ξ₂.1 → IsOne O₁ → IsOne O₂ → (∀ q, Ξ.1 q = Ξ₁.1 q.1 * Ξ₂.1 q.2) → (∀ q, O.1 q = O₁.1 q.1 * O₂.1 q.2) → Λ Ξ = biComb ψ A S A' c c' (Λ O)) ∧ ∀ (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), IsStdChar D ψ (-1) → p.IsCoreFrame B s FA F₀ → (∀ T₀ c (Ξ : Matrix n n' k → ℂ) (a : (n → k) → ℂ) Ψ O, p.IsModel ψ F₀ FS T₀ → p.IsCombAt ψ FA FS c Ξ → Ξ ∈ SB _ → a ∈ SB _ → (∀ x, Ψ.1 x = Ξ x.toCols₁ * a fun r => x r (Sum.inr ())) → (∀ x, O.1 x = Set.indicator {x : Matrix n n' k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) x.toCols₁ * a fun r => x r (Sum.inr ())) → T₀ Ψ = comb ψ B.V₀ S (c.mapDomain fun w => (B.o.resS S).symm (w, 0)) (T₀ O)) ∧ ∀ T₀ c (Ξ : Matrix n' n k → ℂ) (a : (n → k) → ℂ) Ψ O, p.IsModel ψ FS F₀ T₀ → p.IsCombAt ψ FS FA c Ξ → Ξ ∈ SB _ → a ∈ SB _ → (∀ x, Ψ.1 x = Ξ x.toRows₁ * a (x (Sum.inr ()))) → (∀ x, O.1 x = Set.indicator {x : Matrix n' n k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) x.toRows₁ * a (x (Sum.inr ()))) → T₀ Ψ = comb ψ S B.V₀ (c.mapDomain fun w => (B.o.resT S).symm (w, 0)) (T₀ O) := by
  intro D k _ _ _ _ p ψ n n' n'' _ _ _ _ _ _
  refine ⟨?_, ?_⟩
  · intro A S A' FA FS FA' Λ c c' Ξ₁ O₁ Ξ₂ O₂ Ξ O hΛ hc hc' hO₁ hO₂ hΞ hO
    funext u v
    obtain ⟨T₁, hT₁, e₁⟩ := hΛ.1 Ξ₂ v
    let P : SB (Matrix n n' k × Matrix n'' n k) := ⟨_, GlobalTheory.LocFlat.CFac.prodFn_mem_SB O₁.2 Ξ₂.2⟩
    rw [e₁ Ξ₁ Ξ hΞ u, hc.2 T₁ hT₁ O₁ Ξ₁ hO₁ rfl]
    have hf : T₁ O₁ = fun u' => comb ψ S A' c' (Λ O u') v := by
      funext u'
      rw [← e₁ O₁ P (fun q => rfl) u']
      obtain ⟨T₂, hT₂, e₂⟩ := hΛ.2 O₁ u'
      rw [e₂ Ξ₂ P (fun q => rfl) v, hc'.2 T₂ hT₂ O₂ Ξ₂ hO₂ rfl]
      have hg : T₂ O₂ = Λ O u' := funext fun v' => (e₂ O₂ O hO v').symm
      rw [hg]
    rw [hf]
    rfl
  · intro ρ B S s FA F₀ FS _ hF
    refine ⟨?_, ?_⟩
    · intro T₀ c Ξ a Ψ O hT hc hΞ ha hΨ hO
      funext x
      obtain ⟨T₁, hT₁, e⟩ := source_slice_model D k p ψ n n' ρ B S s FA F₀ FS hF T₀ hT a ha (B.o.resS S x).2
      obtain ⟨O₁, hO₁⟩ := exists_isOne (k := k) n n'
      have h1 := hc.2 T₁ hT₁ O₁ ⟨Ξ, hΞ⟩ hO₁ rfl
      have hx : x = (B.o.resS S).symm ((B.o.resS S x).1, (B.o.resS S x).2) := by simp
      rw [hx, e ⟨Ξ, hΞ⟩ Ψ hΨ, h1, comb_resS_slice]
      have hg : T₁ O₁ = fun u' => T₀ O ((B.o.resS S).symm (u', (B.o.resS S x).2)) :=
        funext fun u' => (e O₁ O (fun y => by rw [hO₁]; exact hO y) u').symm
      rw [hg]
    · intro T₀ c Ξ a Ψ O hT hc hΞ ha hΨ hO
      funext x
      obtain ⟨T₁, hT₁, e⟩ := target_slice_model D k p ψ n n' ρ B S s FA F₀ FS hF T₀ hT a ha (B.o.resT S x).2
      obtain ⟨O₁, hO₁⟩ := exists_isOne (k := k) n' n
      have h1 := hc.2 T₁ hT₁ O₁ ⟨Ξ, hΞ⟩ hO₁ rfl
      have hx : x = (B.o.resT S).symm ((B.o.resT S x).1, (B.o.resT S x).2) := by simp
      rw [hx, e ⟨Ξ, hΞ⟩ Ψ hΨ, h1, comb_resT_slice]
      have hg : T₁ O₁ = fun u' => T₀ O ((B.o.resT S).symm (u', (B.o.resT S x).2)) :=
        funext fun u' => (e O₁ O (fun y => by rw [hO₁]; exact hO y) u').symm
      rw [hg]

end GlobalTheory.BiComb
end
end

