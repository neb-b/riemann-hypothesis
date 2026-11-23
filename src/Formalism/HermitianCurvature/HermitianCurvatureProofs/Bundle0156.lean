module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0045
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0063
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0037
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0040
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0152
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0083
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SquareIntegrableGammaZetabarInv
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0058
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnAsm
section
open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField

namespace Formalism.FourierDecayAlt.P.CutMP.En

theorem foldCV_nil (k r : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : ℂ) (H : B.Mat k r → E) :
    foldCV k r s [] H = H := rfl

theorem foldCV_cons (k r : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : ℂ) (x : C.Letter)
    (a : List C.Letter) (H : B.Mat k r → E) :
    foldCV k r s (x :: a) H = s • Q.CV k r (x.2 : ℂ) (foldCV k r s a H) := rfl

theorem foldCV_mem {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Q.Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} {Dm : Set (Q.Mx k r)}
    (hcl : ∀ J ∈ Q.FFl k r z z' π π' 0 Dm, ∀ (Y : ℝ) (s : ℂ), s • Q.CV k r (Y : ℂ) J ∈ Q.FFl k r z z' π π' 0 Dm)
    {J : Q.Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ Q.FFl k r z z' π π' 0 Dm) (s : ℂ) :
    ∀ a : List C.Letter, foldCV k r s a J ∈ Q.FFl k r z z' π π' 0 Dm
  | [] => hJ
  | x :: a => hcl _ (foldCV_mem hcl hJ s a) x.2 s

theorem om_sub {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {g : B.Mat k r} (hg : g ∈ JF.Om k r z z') :
    g ∈ Q.Glev k r 0 ∩ {g | 0 < Formalism.QuantumDeterminants.Gf k r z z' g ∧
      ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} := by
  obtain ⟨hU, hD, hG⟩ := hg
  refine ⟨⟨hU, fun a ha => absurd ha (Nat.not_lt_zero _)⟩, hG, fun a => hD _ ?_⟩
  show (a : ℕ) + 1 ≤ r
  omega

theorem energyTr_of_parts (hR : FoldRev) (hL : AdmLen) (hBF : BesselFoldBuilt) (hL2 : L2BoundAtTowerPlace) (hBe : BetaFrame) :
    EnergyTr := by
  refine ⟨100, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e hFr hcl ε hε hJF a hadm
  have hB' := hB
  obtain ⟨⟨_, _, _, hbuilt, _, _, _, _, _, _, _, _, _⟩, _, _, _⟩ := hB'
  obtain ⟨_, hv⟩ := hbuilt
  obtain ⟨_, _, _, hplace, _, _⟩ := hv v
  have hlen : a.length ≤ S.Ntop := hL E Wp Wq S v a hadm
  set Db := (T v).base with hDb
  set s : ℂ := M.sgn (D.parOf S v) (S.l + 1) with hs
  set F := D.cutF Db χ (f v) ε with hF
  set J₁ := foldCV S.G.k S.G.r s a.reverse (B.JF Db F) with hJ₁
  have hJ₁m : J₁ ∈ Q.FFl S.G.k S.G.r Db.z Db.z' Db.π Db.π' 0 (OmP S T v) := foldCV_mem hcl hJF s _
  have hOpen : IsOpen (OmP S T v) := (isDom_omP Db.z_mem Db.z'_mem).1

  have hae : ∀ᵐ p ∂(volume : Measure ((Fin S.G.r → ℂ) × ℂ)),
      bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') p = 0 ∨
        B.JF Db (foldCV S.G.k S.G.r s a F) (B.gq Db p) = J₁ (B.gq Db p) := by
    have h0 := ae_imp_of_ae_restrict (Formalism.FourierDecayAlt.P.B7.ae_mem_good_set_restrict Db)
    filter_upwards [h0] with p hp
    by_cases hq : p ∈ B.Qset Db
    · right
      have hg := Formalism.FourierDecayAlt.P.big_cell_domain S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Db p (hp hq)
      rw [hBF E Wp Wq S T f χ ν' m₀ top A₀ hB v hcl ε hε hJF a hlen _ hg]
      exact (hR _ _ _ _ _ _ _ _ _ hOpen hcl _ hJF s a _ (om_sub hg)).symm
    · left
      exact le_antisymm (not_lt.1 hq) (Formalism.FourierDecayAlt.P.JCTx2.bcWeight_nonneg' _ _ p)
  have hN1 : jNormSq S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z')
      (fun q => B.hsVec (J₁ (B.gq Db q))) ≠ ⊤ := by
    have h := hL2 E Wp Wq S T f χ ν' m₀ top A₀ hB v ε hε a hlen
    unfold B.normSq at h
    unfold jNormSq at h ⊢
    rwa [lintegral_congr_ae (hae.mono fun p hp => ?_)] at h
    rcases hp with hp | hp
    · rw [show bcWeight S.G.k S.G.r (Tz S.G.k S.G.r (T v).base.z) (Tz S.G.k S.G.r (T v).base.z') p = 0 from hp]
      simp
    · show ENNReal.ofReal (_ * ‖B.hsVec (B.JF Db (foldCV S.G.k S.G.r s a F) (B.gq Db p))‖ ^ 2) = _
      rw [hp]
  have hN2 : jNormSq S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z')
      (fun q => B.hsVec (B.JF Db F (B.gq Db q))) ≠ ⊤ :=
    hL2 E Wp Wq S T f χ ν' m₀ top A₀ hB v ε hε [] (Nat.zero_le _)
  have hBeq := hBe E Wp Wq S T v hplace e hFr J₁ hJ₁m (B.JF Db F) hJF hN1 hN2
  unfold C7.principalHermitianLattice B.beta
  show _ = MA.ipA (D.parOf S v) (trJ S T v e J₁) (trJ S T v e (B.JF Db F))
  rw [← hBeq]
  unfold betaBig
  refine integral_congr_ae (hae.mono fun p hp => ?_)
  rcases hp with hp | hp
  · show ((bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') p : ℝ) : ℂ) * _ =
      ((bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') p : ℝ) : ℂ) * _
    rw [hp]; simp
  · show ((bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') p : ℝ) : ℂ) *
        inner ℂ (B.hsVec (B.JF Db F (B.gq Db p))) (B.hsVec (B.JF Db (foldCV S.G.k S.G.r s a F) (B.gq Db p))) =
      ((bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') p : ℝ) : ℂ) *
        inner ℂ (B.hsVec (B.JF Db F (B.gq Db p))) (B.hsVec (J₁ (B.gq Db p)))
    rw [hp]

end Formalism.FourierDecayAlt.P.CutMP.En
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnBetaFrame
section
open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField
open scoped ContDiff ComplexConjugate

namespace Formalism.FourierDecayAlt.P.CutMP.En

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem toSm_val_of_mem (P : M.Par) {u : MA.Qp P.r P.TT → ℂ} (h : u ∈ MA.smSub P.r P.TT) :
    ((MA.toSm P u : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) = u := by
  unfold MA.toSm; rw [dite_eq_left h]

theorem hsVec_sum_smul {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] {ι : Type} [Fintype ι] (c : ι → ℂ) (e : ι → (W →L[ℂ] V)) :
    B.hsVec (∑ ρ, c ρ • e ρ) = ∑ ρ, c ρ • B.hsVec (e ρ) := by
  change Formalism.FourierDecayAlt.P.JFxI.hsVecL (∑ ρ, c ρ • e ρ) = ∑ ρ, c ρ • Formalism.FourierDecayAlt.P.JFxI.hsVecL (e ρ)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul]

theorem parseval {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] {ι : Type} [Fintype ι] (e : ι → (W →L[ℂ] V))
    (X Y : W →L[ℂ] V) (hX : X = ∑ ρ, inner ℂ (B.hsVec (e ρ)) (B.hsVec X) • e ρ) :
    inner ℂ (B.hsVec Y) (B.hsVec X) =
      ∑ ρ, inner ℂ (B.hsVec (e ρ)) (B.hsVec X) * conj (inner ℂ (B.hsVec (e ρ)) (B.hsVec Y)) := by
  conv_lhs => rw [hX]
  rw [hsVec_sum_smul, inner_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [inner_smul_right, inner_conj_symm]

theorem jgq_contDiffOn {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (hplace : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π')
    {J : Q.Mx S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))}
    (hJ : J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v)) :
    ContDiffOn ℝ ∞ (fun x => J (B.gq (T v).base x)) (MA.Qset (D.parOf S v).r (D.parOf S v).TT) := by
  set Db := (T v).base with hDb
  have hT : Tz S.G.k S.G.r Db.z = S.T := hplace.2.2.2.1
  have hT' : Tz S.G.k S.G.r Db.z' = S.T' := hplace.2.2.2.2.1
  have hQ : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, x ∈ JF.QDom S.G.k S.G.r Db.z Db.z' := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    have h3 : S.T * S.T' < Complex.normSq x.2 := hx.2
    rw [hT, hT']; exact h3
  have hGl : ∀ x ∈ JF.QDom S.G.k S.G.r Db.z Db.z', B.gq Db x ∈ Q.Glev S.G.k S.G.r 0 ∩ OmP S T v := fun x hx =>
    om_sub' (Formalism.FourierDecayAlt.P.big_cell_domain S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Db x hx)
  have hgq : ContDiffOn ℝ ∞ (fun x => B.gq Db x) (JF.QDom S.G.k S.G.r Db.z Db.z') :=
    contDiffOn_infty.2 fun n => Formalism.FourierDecayAlt.P.BigCellOpenDomain.gq_contDiffOn Db n
  refine contDiffOn_of_locally_contDiffOn fun x₀ hx₀ => ?_
  obtain ⟨U, F, hU, hgU, hF, hJF⟩ := hJ.1 _ (hGl x₀ (hQ x₀ hx₀))
  refine ⟨JF.QDom S.G.k S.G.r Db.z Db.z' ∩ (fun x => B.gq Db x) ⁻¹' U,
    hgq.continuousOn.isOpen_inter_preimage (Formalism.FourierDecayAlt.P.BigCellOpenDomain.qdom_open _ _) hU, ⟨hQ x₀ hx₀, hgU⟩, ?_⟩
  have hc : ContDiffOn ℝ ∞ (fun x => F (B.gq Db x))
      (MA.Qset (D.parOf S v).r (D.parOf S v).TT ∩ (JF.QDom S.G.k S.G.r Db.z Db.z' ∩ (fun x => B.gq Db x) ⁻¹' U)) :=
    hF.comp (hgq.mono fun x hx => hx.2.1) fun x hx => hx.2.2
  exact hc.congr fun x hx => hJF _ hx.2.2 (hGl x hx.2.1).1

theorem beta_frame_identity_holds : BetaFrame := by
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T v hplace e hFr J₁ hJ₁ J₂ hJ₂ hN₁ hN₂
  set Db := (T v).base with hDb
  have hT : Tz S.G.k S.G.r Db.z = S.T := hplace.2.2.2.1
  have hT' : Tz S.G.k S.G.r Db.z' = S.T' := hplace.2.2.2.2.1
  have hTT : Tz S.G.k S.G.r Db.z * Tz S.G.k S.G.r Db.z' = (D.parOf S v).TT := by rw [hT, hT']; rfl
  set Qs := MA.Qset (D.parOf S v).r (D.parOf S v).TT with hQs
  have hQm : MeasurableSet Qs := (MA.Qset_open _ _).measurableSet
  set W : (Fin S.G.r → ℂ) × ℂ → ℝ := bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') with hWdef
  have hW0 : ∀ x, 0 ≤ W x := fun x => Formalism.FourierDecayAlt.P.JCTx2.bcWeight_nonneg' _ _ x

  have hW : ∀ x ∈ Qs, W x = Formalism.FourierDecayAlt.P.MAx2.Adj.dR x * MA.wq S.G.k x (D.parOf S v).TT := by
    intro x hx
    have hle : Tz S.G.k S.G.r Db.z * Tz S.G.k S.G.r Db.z' ≤ Complex.normSq x.2 := by
      rw [hTT]; exact le_of_lt hx.2
    rw [hWdef]
    unfold bcWeight
    rw [if_pos hle]
    unfold Formalism.FourierDecayAlt.P.MAx2.Adj.dR MA.wq
    rw [hTT, ← mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun l _ => ?_
    have hM : 2 ≤ MA.Mdim S.G.k S.G.r l := by
      have := l.isLt
      simp only [MA.Mdim]; omega
    have hn : Complex.normSq (x.1 l) ≠ 0 := (Complex.normSq_pos.2 (hx.1 l)).ne'
    have e1 : Formalism.QuantumDeterminants.Mdim S.G.k S.G.r l = MA.Mdim S.G.k S.G.r l := rfl
    rw [e1, pow_mul, Complex.sq_norm, show MA.Mdim S.G.k S.G.r l - 1 = (MA.Mdim S.G.k S.G.r l - 2) + 1 by omega,
      pow_succ]
    field_simp

  have hval : ∀ J ∈ Q.FFl S.G.k S.G.r Db.z Db.z' Db.π Db.π' 0 (OmP S T v), ∀ ρ,
      ((trJ S T v e J ρ : MA.SmQ (D.parOf S v).r (D.parOf S v).TT) : MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ) =
        fun q => ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) *
          inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (J (B.gq Db q.1))) := fun J hJ ρ =>
    toSm_val_of_mem (D.parOf S v) (trace_smoothness E Wp Wq S T v hplace e hFr J hJ ρ)

  have hR : ∀ ρ, MA.ip0 (trJ S T v e J₁ ρ) (trJ S T v e J₂ ρ) =
      ∫ x in Qs, ((W x : ℝ) : ℂ) * (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₁ (B.gq Db x))) *
        conj (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₂ (B.gq Db x))))) := by
    intro ρ
    unfold MA.ip0
    rw [Formalism.FourierDecayAlt.P.MAx2.Adj.integral_base_measure]
    have hz : ∀ x, x ∉ Qs → ((Formalism.FourierDecayAlt.P.MAx2.Adj.dR x : ℝ) : ℂ) *
        MA.ext (r := (D.parOf S v).r) (TT := (D.parOf S v).TT)
          (fun q : MA.Qp (D.parOf S v).r (D.parOf S v).TT =>
            ((trJ S T v e J₁ ρ : MA.SmQ (D.parOf S v).r (D.parOf S v).TT) : MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ) q *
            conj (((trJ S T v e J₂ ρ : MA.SmQ (D.parOf S v).r (D.parOf S v).TT) :
              MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ) q)) x = 0 := by
      intro x hx
      rw [Formalism.FourierDecayAlt.P.MAx2.Adj.ext_out _ hx, mul_zero]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    refine setIntegral_congr_fun hQm fun x hx => ?_
    simp only [MA.ext, hval J₁ hJ₁, hval J₂ hJ₂]
    rw [dite_eq_left (show x ∈ MA.Qset S.G.r (D.parOf S v).TT from hx)]
    rw [hW x hx, map_mul, Complex.conj_ofReal]
    have hw := wq_pos (k := S.G.k) hx
    have hs : ((Real.sqrt (MA.wq S.G.k x (D.parOf S v).TT) : ℝ) : ℂ) *
        ((Real.sqrt (MA.wq S.G.k x (D.parOf S v).TT) : ℝ) : ℂ) = ((MA.wq S.G.k x (D.parOf S v).TT : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hw.le]
    push_cast
    linear_combination ((Formalism.FourierDecayAlt.P.MAx2.Adj.dR x : ℝ) : ℂ) *
      inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₁ (B.gq Db x))) *
        conj (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₂ (B.gq Db x)))) * hs

  have hcont : ∀ J ∈ Q.FFl S.G.k S.G.r Db.z Db.z' Db.π Db.π' 0 (OmP S T v),
      ContinuousOn (fun x => B.hsVec (J (B.gq Db x))) Qs := fun J hJ =>
    hsVec_contDiff.continuous.comp_continuousOn (jgq_contDiffOn S T v hplace hJ).continuousOn
  have heC : ∀ ρ, ContinuousOn (fun x : MA.E S.G.r => B.hsVec (e ρ x.2)) Qs := fun ρ =>
    hsVec_contDiff.continuous.comp_continuousOn
      ((hFr.1 ρ).continuousOn.comp continuous_snd.continuousOn fun x hx => hx.2)
  have hU : ∀ (J) (hJ : J ∈ Q.FFl S.G.k S.G.r Db.z Db.z' Db.π Db.π' 0 (OmP S T v)),
      jNormSq S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') (fun q => B.hsVec (J (B.gq Db q))) ≠ ⊤ →
      IntegrableOn (fun x => W x * ‖B.hsVec (J (B.gq Db x))‖ ^ 2) Qs := by
    intro J hJ hN
    refine ⟨((Formalism.FourierDecayAlt.P.B7.measurable_bcWeight _ _).aestronglyMeasurable).mul
      (((hcont J hJ).norm.pow 2).aestronglyMeasurable hQm), ?_⟩
    refine (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => mul_nonneg (hW0 x) (sq_nonneg _))).2 ?_
    exact lt_of_le_of_lt (setLIntegral_le_lintegral Qs _) (lt_top_iff_ne_top.2 hN)
  have hInt : ∀ ρ, IntegrableOn (fun x => ((W x : ℝ) : ℂ) * (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₁ (B.gq Db x))) *
        conj (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₂ (B.gq Db x)))))) Qs := by
    intro ρ
    refine Integrable.mono' ((hU J₁ hJ₁ hN₁).add (hU J₂ hJ₂ hN₂)) ?_ ?_
    · exact ((Complex.measurable_ofReal.comp (Formalism.FourierDecayAlt.P.B7.measurable_bcWeight _ _)).aestronglyMeasurable).mul
        ((((heC ρ).inner (hcont J₁ hJ₁)).mul ((heC ρ).inner (hcont J₂ hJ₂)).star).aestronglyMeasurable hQm)
    · refine ae_restrict_of_forall_mem hQm fun x hx => ?_
      have he1 : ‖B.hsVec (e ρ x.2)‖ ≤ 1 := by
        have h1 : inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (e ρ x.2)) = (1 : ℂ) := by
          simpa using (hFr.2 x.2 hx.2).2.1 ρ ρ
        rw [inner_self_eq_norm_sq_to_K] at h1
        have h2' : ((‖B.hsVec (e ρ x.2)‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
          rw [Complex.ofReal_pow, Complex.ofReal_one]; exact h1
        have h2 : ‖B.hsVec (e ρ x.2)‖ ^ 2 = 1 := Complex.ofReal_injective h2'
        nlinarith [norm_nonneg (B.hsVec (e ρ x.2))]
      have ha : ∀ J : Q.Mx S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
          ‖inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J (B.gq Db x)))‖ ≤ ‖B.hsVec (J (B.gq Db x))‖ := fun J =>
        (norm_inner_le_norm _ _).trans (by nlinarith [norm_nonneg (B.hsVec (J (B.gq Db x)))])
      have hn1 := ha J₁
      have hn2 := ha J₂
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hW0 x), RCLike.norm_conj]
      have hp : ‖inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₁ (B.gq Db x)))‖ *
          ‖inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₂ (B.gq Db x)))‖ ≤
            ‖B.hsVec (J₁ (B.gq Db x))‖ ^ 2 + ‖B.hsVec (J₂ (B.gq Db x))‖ ^ 2 := by
        nlinarith [norm_nonneg (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₁ (B.gq Db x)))),
          norm_nonneg (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₂ (B.gq Db x)))),
          norm_nonneg (B.hsVec (J₁ (B.gq Db x))), norm_nonneg (B.hsVec (J₂ (B.gq Db x))),
          sq_nonneg (‖B.hsVec (J₁ (B.gq Db x))‖ - ‖B.hsVec (J₂ (B.gq Db x))‖)]
      calc W x * (‖inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₁ (B.gq Db x)))‖ *
            ‖inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₂ (B.gq Db x)))‖)
          ≤ W x * (‖B.hsVec (J₁ (B.gq Db x))‖ ^ 2 + ‖B.hsVec (J₂ (B.gq Db x))‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hp (hW0 x)
        _ = W x * ‖B.hsVec (J₁ (B.gq Db x))‖ ^ 2 + W x * ‖B.hsVec (J₂ (B.gq Db x))‖ ^ 2 := by ring

  unfold MA.ipA
  simp_rw [hR]
  rw [← integral_finsetSum _ (fun ρ _ => hInt ρ)]
  unfold betaBig
  have hae : ∀ᵐ x ∂(volume : Measure ((Fin S.G.r → ℂ) × ℂ)), x ∉ Qs →
      ((W x : ℝ) : ℂ) * inner ℂ (B.hsVec (J₂ (bigCell S.G.k S.G.r x.1 (Db.μsec x.2))))
        (B.hsVec (J₁ (bigCell S.G.k S.G.r x.1 (Db.μsec x.2)))) = 0 := by
    filter_upwards [Formalism.FourierDecayAlt.P.B7.ae_mem_good_set_or_weight_zero Db] with x hx hxQ
    rcases hx with hx | hx
    · exfalso
      apply hxQ
      refine ⟨hx.1, ?_⟩
      have h2 := hx.2
      rw [hTT] at h2
      exact h2
    · rw [show W x = 0 from hx]; simp
  rw [← setIntegral_eq_integral_of_ae_compl_eq_zero hae]
  refine setIntegral_congr_fun hQm fun x hx => ?_
  rw [← Finset.mul_sum]
  congr 1
  have hX := (hFr.2 x.2 hx.2).2.2 (J₁ (B.gq Db x)) (fibre_membership_holds E Wp Wq S T v hplace J₁ hJ₁ x hx)
  exact parseval (fun ρ => e ρ x.2) (J₁ (B.gq Db x)) (J₂ (B.gq Db x)) hX

end Formalism.FourierDecayAlt.P.CutMP.En
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableLoc
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section loc

variable {k r : ℕ} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']

theorem mem_level_zero_of_mem_group {g : B.Mat k r} (hg : g ∈ B.GV k r) : g ∈ Q.Glev k r 0 :=
  ⟨hg, fun a ha => by simp at ha⟩

def LocSm (g₀ : B.Mat k r) (h : B.Mat k r → E') : Prop :=
  ∃ (U : Set (B.Mat k r)) (F : B.Mat k r → E'), IsOpen U ∧ g₀ ∈ U ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F U ∧ ∀ x ∈ U, x ∈ B.GV k r → h x = F x

theorem locSm_of_ckOn {UU : Set (B.Mat k r)} {h : B.Mat k r → E'} (hh : B.CkOn ⊤ UU h) {g₀ : B.Mat k r}
    (hg : g₀ ∈ UU) : LocSm g₀ h := hh g₀ hg

theorem locSm_zero (g₀ : B.Mat k r) : LocSm g₀ (fun _ => (0 : E')) :=
  ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

theorem locSm_add {g₀ : B.Mat k r} {h₁ h₂ : B.Mat k r → E'} (h1 : LocSm g₀ h₁) (h2 : LocSm g₀ h₂) :
    LocSm g₀ (fun x => h₁ x + h₂ x) := by
  obtain ⟨U₁, F₁, o₁, m₁, c₁, e₁⟩ := h1
  obtain ⟨U₂, F₂, o₂, m₂, c₂, e₂⟩ := h2
  exact ⟨U₁ ∩ U₂, fun x => F₁ x + F₂ x, o₁.inter o₂, ⟨m₁, m₂⟩,
    (c₁.mono Set.inter_subset_left).add (c₂.mono Set.inter_subset_right),
    fun x hx hxG => by simp only [e₁ x hx.1 hxG, e₂ x hx.2 hxG]⟩

theorem locSm_smul {g₀ : B.Mat k r} {h : B.Mat k r → E'} (c : ℂ) (h1 : LocSm g₀ h) :
    LocSm g₀ (fun x => c • h x) := by
  obtain ⟨U, F, o, m, cd, e⟩ := h1
  exact ⟨U, fun x => c • F x, o, m, cd.const_smul c, fun x hx hxG => by simp only [e x hx hxG]⟩

theorem locSm_clm {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] {g₀ : B.Mat k r}
    {a : B.Mat k r → (E' →L[ℂ] E₂)} {φ : B.Mat k r → E'} (ha : LocSm g₀ a) (hφ : LocSm g₀ φ) :
    LocSm g₀ (fun x => a x (φ x)) := by
  obtain ⟨U₁, F₁, o₁, m₁, c₁, e₁⟩ := ha
  obtain ⟨U₂, F₂, o₂, m₂, c₂, e₂⟩ := hφ
  refine ⟨U₁ ∩ U₂, fun x => F₁ x (F₂ x), o₁.inter o₂, ⟨m₁, m₂⟩, ?_,
    fun x hx hxG => by simp only [e₁ x hx.1 hxG, e₂ x hx.2 hxG]⟩
  have c₁' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => (F₁ x).restrictScalars ℝ) (U₁ ∩ U₂) :=
    ((ContinuousLinearMap.restrictScalarsL ℂ E' E₂ ℝ ℝ).contDiff.comp_contDiffOn
      (c₁.mono Set.inter_subset_left))
  exact c₁'.clm_apply (c₂.mono Set.inter_subset_right)

theorem locSm_listSum {ι : Type*} {g₀ : B.Mat k r} (l : List ι) (φ : ι → B.Mat k r → E')
    (h : ∀ i ∈ l, LocSm g₀ (φ i)) : LocSm g₀ (fun x => (l.map fun i => φ i x).sum) := by
  induction l with
  | nil => simpa using locSm_zero (E' := E') g₀
  | cons a l ih =>
    simpa using locSm_add (h a (by simp)) (ih fun i hi => h i (by simp [hi]))

theorem ckOn_Rw_top {f : B.Mat k r → E'} (hf : B.CkOn ⊤ (B.GV k r) f) (w : List (B.Mat k r))
    (hw : ∀ X ∈ w, B.inLie k r X) : B.CkOn ⊤ (B.GV k r) (B.Rw w f) := by
  induction w with
  | nil => exact hf
  | cons X w ih =>
    have ih' := ih (fun Y hY => hw Y (by simp [hY]))
    show B.CkOn ⊤ (B.GV k r) (RdV X (B.Rw w f))
    exact Formalism.FourierDecayAlt.P.B5.ckOn_RdV (m := ⊤) (hw X (by simp)) (by rw [top_add]; exact ih')

theorem locSm_smoothLev {O : Set (B.Mat k r)} {h : B.Mat k r → E'}
    (hh : ∀ g₀ ∈ B.GV k r, g₀ ∈ O → LocSm g₀ h) : Q.SmoothLev k r 0 O h := by
  intro g₀ hg₀
  obtain ⟨U, F, o, m, c, e⟩ := hh g₀ hg₀.1.1 hg₀.2
  exact ⟨U, F, o, m, c, fun x hx hxG => e x hx hxG.1⟩

end loc

theorem extension_locality_holds : ExtLoc := by
  intro k r E' _ _ O J hO hJ g₀ hg₀ hg₀O
  obtain ⟨U₀, F, hU₀, hgU₀, hF, hFJ⟩ := hJ g₀ ⟨mem_level_zero_of_mem_group hg₀, hg₀O⟩
  have hV : U₀ ∩ O ∈ nhds g₀ := (hU₀.inter hO).mem_nhds ⟨hgU₀, hg₀O⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hV
  let b : ContDiffBump g₀ := ⟨ε / 3, 2 * ε / 3, by positivity, by linarith⟩
  have hts : tsupport (fun x => b x • F x) ⊆ Metric.closedBall g₀ (2 * ε / 3) :=
    (tsupport_smul_subset_left _ _).trans b.tsupport_eq.subset
  have hcb : Metric.closedBall g₀ (2 * ε / 3) ⊆ U₀ ∩ O := fun x hx =>
    hball (Metric.closedBall_subset_ball (by linarith) hx)
  refine ⟨fun x => b x • F x, Metric.ball g₀ (ε / 3), ?_, ?_, fun x hx => (hcb (hts hx)).2,
    Metric.isOpen_ball, Metric.mem_ball_self (by positivity), ?_⟩
  · intro g _
    refine ⟨Set.univ, fun x => b x • F x, isOpen_univ, trivial, ?_, fun _ _ _ => rfl⟩
    apply ContDiff.contDiffOn
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U₀
    · exact ((b.contDiff.contDiffOn).smul hF).contDiffAt (hU₀.mem_nhds hx)
    · have hx' : x ∉ tsupport (fun x => b x • F x) := fun h => hx (hcb (hts h)).1
      exact (contDiffAt_const (c := (0 : E'))).congr_of_eventuallyEq
        (notMem_tsupport_iff_eventuallyEq.1 hx')
  · exact IsCompact.of_isClosed_subset (isCompact_closedBall g₀ (2 * ε / 3)) (isClosed_tsupport _) hts
  · intro x hx hxG
    have hb : b x = 1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
    have hxU : x ∈ U₀ := (hball (Metric.ball_subset_ball (by linarith) hx)).1
    simp only [hb, one_smul]
    exact (hFJ x hxU (mem_level_zero_of_mem_group hxG)).symm

theorem smooth_operators_holds : SmoothOps := by
  intro k r Wp Wq _ _ _ _ _ D Θ O hO hOP hΘ f hf hs
  have hsupp : closure {g | g ∈ B.GV k r ∧ f g ≠ 0} ⊆ B.GPos D := by
    intro x hx
    have hxG : x ∈ B.GV k r :=
      (Formalism.FourierDecayAlt.P.B5.GV_closed (k := k) (r := r)).closure_subset_iff.2 (by exact fun y hy => hy.1) hx
    have hxT : x ∈ tsupport f := closure_mono (by exact fun y hy => hy.2) hx
    exact hOP x (hs hxT) hxG
  constructor
  · apply locSm_smoothLev
    intro g₀ hg₀ hg₀O
    apply locSm_listSum
    intro T hT
    exact locSm_clm (locSm_of_ckOn (hΘ T hT).1 (hOP g₀ hg₀O hg₀))
      (locSm_of_ckOn (ckOn_Rw_top hf T.word T.word_lie) hg₀)
  · apply locSm_smoothLev
    intro g₀ hg₀ hg₀O
    apply locSm_listSum
    intro T hT
    apply locSm_smul
    have hc : B.CkOn ⊤ (B.GV k r) (fun x => T.coefAdj x (f x)) :=
      Formalism.FourierDecayAlt.P.B5.ckOn_coef (hΘ T hT).2 hf hsupp
    exact locSm_of_ckOn (ckOn_Rw_top hc T.word.reverse
      (fun X hX => T.word_lie X (List.mem_reverse.1 hX))) hg₀

theorem omP_eq (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) (v : Fin S.f) :
    OmP S T v = Q.OmPlus S.G.k S.G.r (T v).base.z (T v).base.z' := by
  ext g
  constructor
  · rintro ⟨hG, hD⟩
    refine ⟨fun l hl => ?_, hG⟩
    rcases Nat.eq_zero_or_pos l.val with h0 | hpos
    · have : l = ⟨0, by omega⟩ := Fin.ext h0
      rw [this]
      rw [show Dmin S.G.k S.G.r (T v).base.z (T v).base.z' g ⟨0, by omega⟩ = 1 by
        unfold Dmin; exact Matrix.det_isEmpty]
      exact one_ne_zero
    · have := hD ⟨l.val - 1, by omega⟩
      have e : (⟨(l.val - 1) + 1, by omega⟩ : Fin (S.G.r + 2)) = l := Fin.ext (by simp; omega)
      simpa [e] using this
  · rintro ⟨hD, hG⟩
    exact ⟨hG, fun a => hD ⟨a.val + 1, by omega⟩ (by have := a.isLt; simp only [Fin.val_mk]; omega)⟩

theorem positive_domain_condition_holds : OmPDom := by
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T v
  refine ⟨?_, fun g hg hgG => ⟨hgG, hg.1⟩⟩
  rw [omP_eq]
  exact Formalism.FourierDecayAlt.P.JCx2.rma_isDom_omPlus (T v).base.z_mem (T v).base.z'_mem

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end

