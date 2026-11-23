module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0171
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0162
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0040
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0048
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0050
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0037
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0170
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0106
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
public import Formalism.FormalDegreeBessel.Bundle0002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenAdelicUnipotentTimesIntegralOutsideSet
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainRecursionFromSingleDescent
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLLocal
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def qOf (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : (Fin r → ℂ) × ℂ :=
  (fun a => Formalism.QuantumDeterminants.cmin k r z z' g a, Formalism.QuantumDeterminants.zeta k r z z' g)

theorem qOf_contOn (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) :
    ContinuousOn (qOf k r z z') (Q.OmPlus k r z z') := by
  refine ContinuousOn.prodMk ?_ ?_
  · refine continuousOn_pi.2 fun a => ?_
    unfold Formalism.QuantumDeterminants.cmin
    exact (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.dmin_cont z z' _).continuousOn.div (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.dmin_cont z z' _).continuousOn
      (fun g hg => hg.1 _ (Nat.le_of_lt a.isLt))
  · unfold Formalism.QuantumDeterminants.zeta
    exact (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.dmin_cont z z' _).continuousOn.div (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.dmin_cont z z' _).continuousOn
      (fun g hg => hg.1 _ le_rfl)

theorem qOf_sgs {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) {p : B.SS k r} (hp : D.inSS p)
    (g : B.Mat k r) : qOf k r D.z D.z' (B.sgs p g) = qOf k r D.z D.z' g := by
  unfold qOf Formalism.QuantumDeterminants.cmin Formalism.QuantumDeterminants.zeta
  simp only [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs D hp]

theorem qOf_gq {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) {q : (Fin r → ℂ) × ℂ}
    (hq : q ∈ JF.QDom k r D.z D.z') : qOf k r D.z D.z' (B.gq D q) = q :=
  Prod.ext (funext fun a => Formalism.FourierDecayAlt.P.BigCellZetaMinors.cmin_gq D hq a) (Formalism.FourierDecayAlt.P.BigCellZetaMinors.zeta_gq D hq)

theorem self_adjoint_locality_holds : SALocal := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v Θ _hΘ K hK V hV hVQ hK0 y hy
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  let O : Set (B.Mat S.G.k S.G.r) := Q.OmPlus S.G.k S.G.r (T v).base.z (T v).base.z' ∩
    qOf S.G.k S.G.r (T v).base.z (T v).base.z' ⁻¹' V
  have hOo : IsOpen O :=
    (qOf_contOn _ _ _ _).isOpen_inter_preimage (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open _ _) hV
  have hD : ∀ x ∈ JF.Om S.G.k S.G.r (T v).base.z (T v).base.z', x ∈ Q.Glev S.G.k S.G.r 0 ∩
      {g | 0 < Gf S.G.k S.G.r (T v).base.z (T v).base.z' g ∧
        ∀ a : Fin S.G.r, Dmin S.G.k S.G.r (T v).base.z (T v).base.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} :=
    fun x hx => ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hx.1, Formalism.FourierDecayAlt.P.CutMP.jdc_of_om _ _ hx⟩
  have hNl : ∀ n ∈ Formalism.QuantumDeterminants.Nset S.G.k S.G.r, n ∈ Q.Nlev S.G.k S.G.r 0 :=
    fun n hn => ⟨hn, Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hn.1⟩
  have hKz : ∀ x ∈ B.GV S.G.k S.G.r, x ∈ O → K x = 0 := by
    intro x hxG hxO
    have hxOm : x ∈ JF.Om S.G.k S.G.r (T v).base.z (T v).base.z' := ⟨hxG, hxO.1⟩
    obtain ⟨p, hp, q, hq, rfl⟩ := Formalism.FourierDecayAlt.P.psiOnto_true _ _ _ _ (T v).base _ hxOm
    have hqV : q ∈ V := by
      have h1 : qOf S.G.k S.G.r (T v).base.z (T v).base.z' (B.sgs p (B.gq (T v).base q)) ∈ V := hxO.2
      rwa [qOf_sgs (T v).base hp, qOf_gq (T v).base hq] at h1
    have hgq := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq
    have := LT.agree_sgs (T v).base K (fun _ => 0)
      (fun y hy n hn => hK.2.1 y (hD y hy) n (hNl n hn))
      (fun y hy n hn => hK.2.2.1 y (hD y hy) n (hNl n hn))
      (fun y hy h hh h' hh' => hK.2.2.2 y (hD y hy) h hh h' hh')
      (fun _ _ _ _ => (smul_zero _).symm) (fun _ _ _ _ => (smul_zero _).symm)
      (fun _ _ _ _ _ _ => by simp)
      hp hgq (hK0 q hqV)
    exact this
  have hyQ : y ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' :=
    ⟨(hVQ hy).1, by rw [← hTT]; exact (hVQ hy).2⟩
  have hg0 := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hyQ
  have hg0O : B.gq (T v).base y ∈ O := by
    refine ⟨hg0.2, ?_⟩
    show qOf S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base y) ∈ V
    rw [qOf_gq (T v).base hyQ]; exact hy
  unfold B.opApply
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨Tm, _, rfl⟩ := List.mem_map.1 hx
  rw [Formalism.FourierDecayAlt.P.BetaSesquilinearity.Rw_vanish hOo Tm.word_lie hKz _ hg0.1 hg0O, map_zero]

end Formalism.FourierDecayAlt.P.CutMP.JA.SA

end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLQOf
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

variable {k r : ℕ}

def qOf (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : (Fin r → ℂ) × ℂ :=
  (fun a => Formalism.QuantumDeterminants.cmin k r z z' g a, Formalism.QuantumDeterminants.zeta k r z z' g)

theorem qOf_contOn (z z' : Fin (2 * r + k + 1) → ℂ) : ContinuousOn (qOf z z') (Q.OmPlus k r z z') := by
  refine ContinuousOn.prodMk ?_ ?_
  · refine continuousOn_pi.2 fun a => ?_
    show ContinuousOn (fun g : B.Mat k r => Dmin k r z z' g ⟨a.val + 1, by omega⟩ / Dmin k r z z' g ⟨a.val, by omega⟩) _
    exact (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.dmin_cont z z' _).continuousOn.div (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.dmin_cont z z' _).continuousOn
      fun g hg => hg.1 ⟨a.val, by omega⟩ (by simp)
  · show ContinuousOn (fun g : B.Mat k r => Dmin k r z z' g (Fin.last (r + 1)) / Dmin k r z z' g ⟨r, by omega⟩) _
    exact (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.dmin_cont z z' _).continuousOn.div (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.dmin_cont z z' _).continuousOn
      fun g hg => hg.1 ⟨r, by omega⟩ le_rfl

theorem isOpen_qOf (z z' : Fin (2 * r + k + 1) → ℂ) {U : Set ((Fin r → ℂ) × ℂ)} (hU : IsOpen U) :
    IsOpen (Q.OmPlus k r z z' ∩ qOf z z' ⁻¹' U) :=
  (qOf_contOn z z').isOpen_inter_preimage (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open z z') hU

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem qOf_sgs (Bs : B.RealPlaceData k r Wp Wq) {p : B.SS k r} (hp : Bs.inSS p) (g : B.Mat k r) :
    qOf Bs.z Bs.z' (B.sgs p g) = qOf Bs.z Bs.z' g := by
  unfold qOf Formalism.QuantumDeterminants.cmin Formalism.QuantumDeterminants.zeta
  simp only [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp]

theorem qOf_gq (Bs : B.RealPlaceData k r Wp Wq) {q : (Fin r → ℂ) × ℂ} (hq : q ∈ JF.QDom k r Bs.z Bs.z') :
    qOf Bs.z Bs.z' (B.gq Bs q) = q :=
  Prod.ext (funext fun a => Formalism.FourierDecayAlt.P.BigCellZetaMinors.cmin_gq Bs hq a) (Formalism.FourierDecayAlt.P.BigCellZetaMinors.zeta_gq Bs hq)

theorem om_eq_sgs (Bs : B.RealPlaceData k r Wp Wq) {g : B.Mat k r} (hg : g ∈ JF.Om k r Bs.z Bs.z') :
    ∃ p, Bs.inSS p ∧ qOf Bs.z Bs.z' g ∈ JF.QDom k r Bs.z Bs.z' ∧ g = B.sgs p (B.gq Bs (qOf Bs.z Bs.z' g)) := by
  obtain ⟨p, hp, q, hq, rfl⟩ := Formalism.FourierDecayAlt.P.psiOnto_true k r Wp Wq Bs g hg
  rw [qOf_sgs Bs hp, qOf_gq Bs hq]
  exact ⟨p, hp, hq, rfl⟩

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem agree_qOf (Bs : B.RealPlaceData k r Wp Wq) (J F : B.Mat k r → (Wq →L[ℂ] Wp)) (U : Set ((Fin r → ℂ) × ℂ))
    (hJ : J ∈ Q.FFl k r Bs.z Bs.z' Bs.π Bs.π' 0 {g | 0 < Gf k r Bs.z Bs.z' g ∧
      ∀ a : Fin r, Dmin k r Bs.z Bs.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0})
    (hag : ∀ q ∈ JF.QDom k r Bs.z Bs.z', q ∈ U → J (B.gq Bs q) = B.JF Bs F (B.gq Bs q)) :
    ∀ g ∈ JF.Om k r Bs.z Bs.z', qOf Bs.z Bs.z' g ∈ U → J g = B.JF Bs F g := by
  intro g hg hgU
  obtain ⟨p, hp, hq, hge⟩ := om_eq_sgs Bs hg
  set q := qOf Bs.z Bs.z' g with hqdef
  rw [hge]
  have hgq := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom Bs hq
  have hD : ∀ y ∈ JF.Om k r Bs.z Bs.z', y ∈ Q.Glev k r 0 ∩ {g | 0 < Gf k r Bs.z Bs.z' g ∧
      ∀ a : Fin r, Dmin k r Bs.z Bs.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} := fun y hy =>
    ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hy.1, Formalism.FourierDecayAlt.P.CutMP.jdc_of_om _ _ hy⟩
  have hNl : ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, n ∈ Q.Nlev k r 0 := fun n hn => ⟨hn, Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hn.1⟩
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarW'
  have hN := bessel_unipotent_equiv_holds Wp Wq k r Bs.z Bs.z' cStd Bs.π Bs.π' Bs.μW Bs.μN Bs.μW' F Bs.z_mem Bs.z'_mem
    Bs.haarN.conc (fun n₀ h => Bs.haarN.left n₀ h)
  refine LT.agree_sgs Bs J (B.JF Bs F)
    (fun y hy n hn => hJ.2.1 y (hD y hy) n (hNl n hn))
    (fun y hy n hn => hJ.2.2.1 y (hD y hy) n (hNl n hn))
    (fun y hy h hh h' hh' => hJ.2.2.2 y (hD y hy) h hh h' hh')
    (fun y _ n hn => ?_) (fun y _ n hn => ?_)
    (fun y _ h hh h' hh' => Formalism.FourierDecayAlt.P5.jf_uEquiv Bs F y hh hh')
    hp hgq (hag q hq hgU)
  · have e := hN y n hn 1 WeylGroupFacts.mem_n_one
    rw [Matrix.mul_one, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one Bs.z'_mem, mul_one] at e
    exact e
  · have e := hN y 1 WeylGroupFacts.mem_n_one n hn
    rw [Matrix.one_mul, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one Bs.z_mem, one_mul] at e
    exact e

end Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO

end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASASecCover
section
open Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem self_adjoint_cover_holds : SACover := by
  intro k r z z' hz hz' g hg
  obtain ⟨hg0, hD, hG⟩ := hg
  obtain ⟨n, hn, n', hn', c, hc, μ, hμ, hgeq⟩ := Formalism.FourierDecayAlt.P.big_cell_decomposition k r z z' g hg0.1 hD
  have e : bigCell k r c μ = wCell k r (Fin.last r) c * B2.embWb k r μ := by
    rw [Formalism.FourierDecayAlt.P5.Rad.wCell_last_eq, ← (Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization k r c μ).1]
  have hg1 : B2.embWb k r μ ∈ Glev k r (Fin.last r) :=
    Formalism.FourierDecayAlt.P.NFRadRedA.uwb_glev (Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_mem_UWb hμ)
  have hninv : n⁻¹ ∈ Nset k r := Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hn

  have hDinv : ∀ l, Dmin k r z z' g l = Dmin k r z z' (bigCell k r c μ) l := by
    intro l
    rw [hgeq]
    exact dInv k r z z' hz hz' _ (Formalism.FourierDecayAlt.P.BigCellDecomposition.n_inv_S hn) _ (Formalism.FourierDecayAlt.P.BigCellDecomposition.n_S hn') _ l
  have hGb : 0 < Gf k r z z' (bigCell k r c μ) := by
    have e2 : Gf k r z z' g = Gf k r z z' (bigCell k r c μ) := by
      unfold Gf; rw [hDinv, hDinv]
    rw [← e2]; exact hG
  have hGG : 0 < GGl k r z z' (B2.embWb k r μ) := by
    have hmin := big_cell_minors_holds k r z z' c μ hz hz'
    have hζ : herm (Hpk k r) (bigCell k r c μ *ᵥ z') z = zetaL k r z z' (Fin.last r) (B2.embWb k r μ) := by
      rw [Formalism.FourierDecayAlt.P5.Rad.zetaL_last, ← Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart hz', Formalism.FourierDecayAlt.P.BigCellHermitian.bigCell_mulVec_jV,
        Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_mulVec_jV]
    have hzeta := hmin.2.2 hc
    rw [hζ] at hzeta
    have hr := hmin.1 (Fin.last r)
    set Pd := Dmin k r z z' (bigCell k r c μ) ⟨r, by omega⟩ with hPd
    have hP0 : Pd ≠ 0 := by
      have : Pd = ∏ a : Fin r with a.val < (Fin.last r).val, c a := hr
      rw [this]; exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
    have hlast : Dmin k r z z' (bigCell k r c μ) (Fin.last (r + 1)) =
        zetaL k r z z' (Fin.last r) (B2.embWb k r μ) * Pd := by
      unfold Formalism.QuantumDeterminants.zeta at hzeta
      rw [← hPd] at hzeta
      have h2 := div_mul_cancel₀ (Dmin k r z z' (bigCell k r c μ) (Fin.last (r + 1))) hP0
      rw [hzeta] at h2
      exact h2.symm
    have hGb' := hGb
    unfold Gf at hGb'
    rw [hlast, ← hPd, Complex.normSq_mul] at hGb'
    have h1 : 0 < Complex.normSq Pd := Complex.normSq_pos.2 hP0
    unfold GGl
    nlinarith
  refine ⟨n⁻¹, ⟨hninv, hninv.1, fun a ha => absurd ha (Nat.not_lt_zero _)⟩, n', ⟨hn', hn'.1, fun a ha => absurd ha (Nat.not_lt_zero _)⟩,
    c, hc, B2.embWb k r μ, hg1, hGG, ?_⟩
  rw [hgeq, e]

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASASecDesc
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ContDiff ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA.Desc

open Formalism.FourierDecayAlt.P.Qx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section fam

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {k r : ℕ}

def EqvL (z z' : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq))
    (i : Fin (r + 1)) (D : Set (Mx k r)) (J : Mx k r → (Wq →L[ℂ] Wp)) : Prop :=
  LeftEq k r z i D J ∧ RightEq k r z' i D J ∧
    ∀ g ∈ Glev k r i ∩ D, ∀ h ∈ UWset k r z, ∀ h' ∈ UWset k r z', J (h * g * h') = (π h).comp ((J g).comp (π' h'))

def FamD (z z' : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq))
    (i : Fin (r + 1)) (D : Set (Mx k r)) (Φ : Fn k r (Wq →L[ℂ] Wp)) : Prop :=
  (∀ c ∈ OmX r, EqvL z z' π π' i D (Φ c)) ∧
  ∀ c₀ ∈ OmX r, ∀ g₀ ∈ Glev k r i ∩ D, ∃ (U : Set ((Fin r → ℂ) × Mx k r)) (F : (Fin r → ℂ) × Mx k r → (Wq →L[ℂ] Wp)),
    IsOpen U ∧ (c₀, g₀) ∈ U ∧ ContDiffOn ℝ ∞ F U ∧
      ∀ x ∈ U, x.1 ∈ OmX r → x.2 ∈ Glev k r i → x.2 ∈ D → Φ x.1 x.2 = F x

theorem famD_FFl {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
    {i : Fin (r + 1)} {D : Set (Mx k r)} (hD : IsOpen D) {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : FamD z z' π π' i D Φ)
    {c : Fin r → ℂ} (hc : c ∈ OmX r) : Φ c ∈ FFl k r z z' π π' i D := by
  refine ⟨?_, (hΦ.1 c hc).1, (hΦ.1 c hc).2.1, (hΦ.1 c hc).2.2⟩
  intro g₀ hg₀
  obtain ⟨U, F, hU, hx, hF, hΦF⟩ := hΦ.2 c hc g₀ hg₀
  refine ⟨(fun g => (c, g)) ⁻¹' U ∩ D, fun g => F (c, g), (hU.preimage (by fun_prop)).inter hD, ⟨hx, hg₀.2⟩, ?_,
    fun g hg hgl => hΦF (c, g) hg.1 hc hgl hg.2⟩
  exact hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun g hg => hg.1)

theorem upd_mem {c : Fin r → ℂ} (hc : c ∈ OmX r) {c'' : ℂ} (h : c'' ≠ 0) (l : Fin r) :
    Function.update c l c'' ∈ OmX r := by
  intro a
  by_cases ha : a = l
  · subst ha; simpa using h
  · simpa [Function.update_apply, ha] using hc a

def JxF (l : Fin r) (z z' : Fin (2 * r + k + 1) → ℂ) (Φ : Fn k r (Wq →L[ℂ] Wp)) : Fn k r (Wq →L[ℂ] Wp) :=
  fun c g => (psi k r z cStd (uL k r l g) * psi k r z' cStd (iH (uL k r l (iH g)))) •
    Φ (Function.update c l (cF k r l g)) (rho k r l g)

theorem dec_JxF {l : Fin r} {g u g₁ u' : Mx k r} {c' : ℂ} (h : Dec k r l g c' u g₁ u')
    (z z' : Fin (2 * r + k + 1) → ℂ) (Φ : Fn k r (Wq →L[ℂ] Wp)) (c : Fin r → ℂ) :
    JxF l z z' Φ c g = (psi k r z cStd u * psi k r z' cStd u') • Φ (Function.update c l c') g₁ := by
  unfold JxF
  rw [h.uL_eq, h.uL_iH, h.cF_eq, h.rho_eq, iH_eq (up_inv h.hu').1.1, inv_inv' h.hu'.1.1]

theorem descended_function_apply_w1_mul {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (l : Fin r)
    (Φ : Fn k r (Wq →L[ℂ] Wp)) (c : Fin r → ℂ) {c' : ℂ} (hc' : c' ≠ 0) {g : Mx k r} (hg : g ∈ Glev k r l.succ) :
    JxF l z z' Φ c (w1 k r l c' * g) = Φ (Function.update c l c') g := by
  rw [dec_JxF (dec_w hc' hg), psi_one hz, psi_one hz', one_mul, one_smul]

theorem w1_mul_mem_descended_set_iff (l : Fin r) (D₁ : Set (Mx k r)) {c : ℂ} (hc : c ≠ 0) {g : Mx k r} (hg : g ∈ Glev k r l.succ) :
    w1 k r l c * g ∈ D0 k r l D₁ ↔ g ∈ D₁ := by
  have d := dec_w (l := l) hc hg
  constructor
  · intro h
    have h2 : rho k r l (w1 k r l c * g) ∈ D₁ := h.2
    rwa [d.rho_eq] at h2
  · intro h
    refine ⟨d.cell_decomposition_mem, ?_⟩
    show rho k r l (w1 k r l c * g) ∈ D₁
    rw [d.rho_eq]; exact h

theorem smM_snd (s : Set ((Fin r → ℂ) × Mx k r)) : SmM (fun x : (Fin r → ℂ) × Mx k r => x.2) s := fun i j =>
  ((contDiff_apply_apply ℝ i j).comp contDiff_snd).contDiffOn

theorem descended_set_is_domain {z z' : Fin (2 * r + k + 1) → ℂ} (l : Fin r) {D₁ : Set (Mx k r)} (hD₁ : IsDom k r z z' l.succ D₁) :
    IsDom k r z z' l.castSucc (D0 k r l D₁) := by
  refine ⟨isOpen_cell_domain hD₁.1, ?_⟩
  rintro g hg s ⟨h, hh, m, hm, rfl⟩ s' ⟨h', hh', m', hm', rfl⟩
  obtain ⟨c, u, g₁, u', d, hg₁⟩ := mem_cell_domain_iff.1 hg
  obtain ⟨u₂, hu₂, n₁, hn₁, rfl⟩ := nlev_dec hm
  obtain ⟨u₃, hu₃, n₃, hn₃, rfl⟩ := nlev_dec' hm'
  have d1 := (((((d.leftG hn₁.2).leftU hu₂).leftG (uw_glev hh _)).rightG (uw_glev hh' _)).rightG hn₃.2).rightU hu₃
  have e : h * (u₂ * n₁) * g * (h' * (n₃ * u₃)) = h * (u₂ * (n₁ * g)) * h' * n₃ * u₃ := by
    simp only [Matrix.mul_assoc]
  rw [e]
  refine (mem_cell_domain_iff.2 ⟨_, _, _, _, d1, ?_⟩).2
  have h2 := hD₁.2 g₁ ⟨d.hg, hg₁⟩ (h * n₁) ⟨h, hh, n₁, hn₁, rfl⟩ (h' * n₃) ⟨h', hh', n₃, hn₃, rfl⟩
  have e2 : h * (n₁ * g₁) * h' * n₃ = h * n₁ * g₁ * (h' * n₃) := by simp only [Matrix.mul_assoc]
  rw [e2]; exact h2

theorem famStep {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
    (hz : inWb k r z) (hz' : inWb k r z') (l : Fin r) {D₁ : Set (Mx k r)}
    {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : FamD z z' π π' l.succ D₁ Φ) :
    FamD z z' π π' l.castSucc (D0 k r l D₁) (JxF l z z' Φ) := by
  refine ⟨fun c hc => ⟨?_, ?_, ?_⟩, ?_⟩
  ·
    intro g hg n hn
    obtain ⟨c'', u, g₁, u', d, hg₁⟩ := mem_cell_domain_iff.1 hg
    obtain ⟨u₂, hu₂, n₁, hn₁, rfl⟩ := nlev_dec hn
    have d1 := (d.leftG hn₁.2).leftU hu₂
    have hL := (hΦ.1 _ (upd_mem hc d.hc l)).1 g₁ ⟨d.hg, hg₁⟩ n₁ hn₁
    rw [Matrix.mul_assoc, dec_JxF d1, dec_JxF d, hL,
      psi_mul hz (up_nset hu₂) (up_nset (up_conj d.hu hn₁.2)), psi_conjN hz hn₁.1 (up_nset d.hu),
      psi_mul hz (up_nset hu₂) hn₁.1]
    simp only [smul_smul]
    congr 1
    ring
  ·
    intro g hg n hn
    obtain ⟨c'', u, g₁, u', d, hg₁⟩ := mem_cell_domain_iff.1 hg
    obtain ⟨u₃, hu₃, n₃, hn₃, rfl⟩ := nlev_dec' hn
    have d1 := (d.rightG hn₃.2).rightU hu₃
    have hR := (hΦ.1 _ (upd_mem hc d.hc l)).2.1 g₁ ⟨d.hg, hg₁⟩ n₃ hn₃
    rw [← Matrix.mul_assoc, dec_JxF d1, dec_JxF d, hR,
      psi_mul hz' (up_nset (up_conj' d.hu' hn₃.2)) (up_nset hu₃), psi_conjN' hz' hn₃.1 (up_nset d.hu'),
      psi_mul hz' hn₃.1 (up_nset hu₃)]
    simp only [smul_smul]
    congr 1
    ring
  ·
    intro g hg h hh h' hh'
    obtain ⟨c'', u, g₁, u', d, hg₁⟩ := mem_cell_domain_iff.1 hg
    have d1 := (d.leftG (uw_glev hh _)).rightG (uw_glev hh' _)
    have hW := (hΦ.1 _ (upd_mem hc d.hc l)).2.2 g₁ ⟨d.hg, hg₁⟩ h hh h' hh'
    rw [dec_JxF d1, dec_JxF d, hW, psi_conjW hz hh (up_nset d.hu), psi_conjW' hz' hh' (up_nset d.hu')]
    ext v
    simp
  ·
    intro c₀ hc₀ g₀ hg₀
    obtain ⟨c'', u, g₁, u', d, hg₁⟩ := mem_cell_domain_iff.1 hg₀
    obtain ⟨U₁, F₁, hU₁, hmem, hF₁, hag⟩ := hΦ.2 (Function.update c₀ l c'') (upd_mem hc₀ d.hc l) g₁ ⟨d.hg, hg₁⟩
    have hs0 : IsOpen {x : (Fin r → ℂ) × Mx k r | x.2 ∈ C0 k r l} := isOpen_adelicUnipotentTimesIntegralOutsideSet.preimage continuous_snd
    have h1 := smM_snd (k := k) (r := r) {x : (Fin r → ℂ) × Mx k r | x.2 ∈ C0 k r l}
    have hupd : ContDiffOn ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => Function.update x.1 l (cF k r l x.2))
        {x : (Fin r → ℂ) × Mx k r | x.2 ∈ C0 k r l} := by
      refine contDiffOn_pi.2 fun a => ?_
      by_cases ha : a = l
      · subst ha
        exact (sm_cF (l := a) h1).congr fun x _ => by simp
      · exact ((contDiff_apply ℝ (fun _ => ℂ) a).comp contDiff_fst).contDiffOn.congr fun x _ => by
          simp [ha]
    have hrho : ContDiffOn ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => rho k r l x.2)
        {x : (Fin r → ℂ) × Mx k r | x.2 ∈ C0 k r l} :=
      (smM_contDiffOn smM_rho).comp contDiff_snd.contDiffOn fun x hx => hx
    have hm := hupd.prodMk hrho
    refine ⟨{x : (Fin r → ℂ) × Mx k r | x.2 ∈ C0 k r l} ∩
        (fun x : (Fin r → ℂ) × Mx k r => (Function.update x.1 l (cF k r l x.2), rho k r l x.2)) ⁻¹' U₁,
      fun x => (psi k r z cStd (uL k r l x.2) * psi k r z' cStd (iH (uL k r l (iH x.2)))) •
        F₁ (Function.update x.1 l (cF k r l x.2), rho k r l x.2),
      hm.continuousOn.isOpen_inter_preimage hs0 hU₁, ⟨d.cell_decomposition_mem, ?_⟩, ?_, ?_⟩
    · show (Function.update c₀ l (cF k r l g₀), rho k r l g₀) ∈ U₁
      rw [d.cF_eq, d.rho_eq]; exact hmem
    · have hs : {x : (Fin r → ℂ) × Mx k r | x.2 ∈ C0 k r l} ∩
          (fun x : (Fin r → ℂ) × Mx k r => (Function.update x.1 l (cF k r l x.2), rho k r l x.2)) ⁻¹' U₁ ⊆
          {x : (Fin r → ℂ) × Mx k r | x.2 ∈ C0 k r l} := Set.inter_subset_left
      have h1' := smM_snd (k := k) (r := r) ({x : (Fin r → ℂ) × Mx k r | x.2 ∈ C0 k r l} ∩
          (fun x : (Fin r → ℂ) × Mx k r => (Function.update x.1 l (cF k r l x.2), rho k r l x.2)) ⁻¹' U₁)
      have h2 : SmM (fun x : (Fin r → ℂ) × Mx k r => uL k r l x.2) _ := smM_uL h1' fun x hx => hx.1.1
      have h3 : SmM (fun x : (Fin r → ℂ) × Mx k r => uL k r l (iH x.2)) _ := smM_uL (smM_iH h1') fun x hx => hx.1.2
      have h5 := hF₁.comp (hm.mono hs) fun x hx => hx.2
      exact ((sm_psi z cStd h2).mul (sm_psi z' cStd (smM_iH h3))).smul h5
    · intro x hxU hx1 hxG hxD
      obtain ⟨u3, g3, u3', d3⟩ := dec_exists hxG hxU.1.1
      have hy := hag (Function.update x.1 l (cF k r l x.2), rho k r l x.2) hxU.2 (upd_mem hx1 hxU.1.1 l)
        (by show rho k r l x.2 ∈ Glev k r l.succ; rw [d3.rho_eq]; exact d3.hg) hxD.2
      show JxF l z z' Φ x.1 x.2 = _
      unfold JxF
      rw [hy]

end fam

end Formalism.FourierDecayAlt.P.CutMP.JA.SA.Desc
end
end

