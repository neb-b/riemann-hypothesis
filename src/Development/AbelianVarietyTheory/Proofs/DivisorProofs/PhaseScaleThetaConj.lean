module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1802
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2804
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1815
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0509

@[expose] public section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

section CorePart

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open GlobalTheory.SeriesTie GlobalTheory.SeriesTie.BaseRat GlobalTheory.BigOn.Exp
open Formalism.L2.Host (embLL0)
open scoped TensorProduct

namespace GlobalTheory.SerSmall

variable {D : D7}

section Comb

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
  {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
  (j : Fin D.R.m)

def SmallComb (φ : GA D (Wc D j) → ℂ) : Prop :=
  ∃ (n : ℕ) (z : Fin n → ℂ) (g : Fin n → NX.FmK S ((j : ℕ) + 1)), (∀ k, z k ∈ (embLL0 D).fieldRange) ∧
    φ = ∑ k, z k • evW YS v₀ j (g k).val

variable {YS v₀ j}

theorem SmallComb.zero : SmallComb YS v₀ j 0 :=
  ⟨0, Fin.elim0, Fin.elim0, fun k => Fin.elim0 k, by rw [Finset.univ_eq_empty, Finset.sum_empty]⟩

theorem SmallComb.add {φ ψ : GA D (Wc D j) → ℂ} (h1 : SmallComb YS v₀ j φ) (h2 : SmallComb YS v₀ j ψ) :
    SmallComb YS v₀ j (φ + ψ) := by
  obtain ⟨n, z, g, hz, rfl⟩ := h1
  obtain ⟨m, z', g', hz', rfl⟩ := h2
  refine ⟨n + m, Fin.append z z', Fin.append g g', fun k => ?_, ?_⟩
  · refine Fin.addCases (fun a => ?_) (fun a => ?_) k
    · rw [Fin.append_left]; exact hz a
    · rw [Fin.append_right]; exact hz' a
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]

theorem SmallComb.smul {φ : GA D (Wc D j) → ℂ} (h : SmallComb YS v₀ j φ) {a : ℂ} (ha : a ∈ (embLL0 D).fieldRange) :
    SmallComb YS v₀ j (a • φ) := by
  obtain ⟨n, z, g, hz, rfl⟩ := h
  refine ⟨n, fun k => a * z k, g, fun k => mul_mem ha (hz k), ?_⟩
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun k _ => smul_smul _ _ _

theorem smallComb_of_small {ρ : Setup D.ntw} {i : D.ntw.Tw} {b : Bool}
    (Φ : PolF D (Wc D j).rank (Vc D j).rank →ₗ[ℂ] (GA D (Wc D j) → ℂ))
    (hinj : ∀ P ∈ (ρ.B i j b).valSpace, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P = 0 → P = 0)
    (honto : ∀ F : VV ↥D.LL0 (ρ.B i j b).w.lam, ∃ P ∈ (ρ.B i j b).valSpace, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P =
      coefFn (embLL0 D) (ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank))
    (hΦ : ∀ P ∈ (ρ.B i j b).valSpace, ∀ F : VV ↥D.LL0 (ρ.B i j b).w.lam, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P =
      coefFn (embLL0 D) (ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) → SmallComb YS v₀ j (Φ P))
    {h : GA D (Vc D j)} {P : PolF D (Wc D j).rank (Vc D j).rank} (hP : P ∈ ρ.lat i j b (GlobalTheory.BigOn.Exp.smallInt D) h) :
    SmallComb YS v₀ j (Φ P) := by
  have key : ∀ φ ∈ coefLatFn (embLL0 D) (labLL0 D) (GlobalTheory.BigOn.Exp.smallInt D) (ρ.B i j b).w.lam ((ρ.B i j b).latAt (finPt _ h)),
      ∃ P' ∈ (ρ.B i j b).valSpace, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P' = φ ∧ SmallComb YS v₀ j (Φ P') := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem _ h1 =>
      obtain ⟨F, -, rfl⟩ := h1
      obtain ⟨P', h2, h3⟩ := honto F
      exact ⟨P', h2, h3, hΦ P' h2 F h3⟩
    | zero => exact ⟨0, zero_mem _, map_zero _, by rw [map_zero]; exact SmallComb.zero⟩
    | add _ _ _ _ h1 h2 =>
      obtain ⟨P₁, a1, rfl, f₁⟩ := h1
      obtain ⟨P₂, a2, rfl, f₂⟩ := h2
      exact ⟨P₁ + P₂, add_mem a1 a2, map_add _ _ _, by rw [map_add (f := _)]; exact f₁.add f₂⟩
    | smul c _ _ h1 =>
      obtain ⟨P₁, a1, rfl, f₁⟩ := h1
      refine ⟨(c : ℂ) • P₁, Submodule.smul_mem _ _ a1, ?_, ?_⟩
      · rw [map_smul]; rfl
      · rw [map_smul]; exact f₁.smul (by obtain ⟨a, ha⟩ := c.2; exact ⟨_, ha⟩)
  obtain ⟨P', h1, h2, h3⟩ := key _ hP.2
  rwa [sub_eq_zero.1 (hinj (P - P') (sub_mem hP.1 h1) (by rw [map_sub, h2]; exact sub_self _))]

end Comb

theorem delAt_mem (C : Formalism.L2.Host.CharFrame D) (hval : Formalism.L2.Host.ValLL0 D C) (l : ℕ) {δc : (AE D)ˣ →* Circle}
    (h : ChrEq δc (C.delAt l)) (x : (AE D)ˣ) : ((δc x : Circle) : ℂ) ∈ (embLL0 D).fieldRange := by
  have key : (∃ n : ℕ, 0 < n ∧ (C.delAt l).OrderDvd n) ∧ (C.delAt l).ValuesIn 0 (embLL0 D) := by
    unfold Formalism.L2.Host.CharFrame.delAt
    split_ifs
    exacts [⟨C.isDel'.fin, hval.del'⟩, ⟨C.isDel.fin, hval.del⟩]
  obtain ⟨⟨n, hn, ho⟩, hv⟩ := key
  obtain ⟨y, hy⟩ := GlobalTheory.Adopt.heckeCharacter_finiteOrder_values_in_field D δc _ n _ (embLL0 D) h hn ho hv x
  exact ⟨y, hy⟩

section Main

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {Rl : RealDat3 D A3 T.Q.c.F} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
  {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)}
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

theorem smallComb_of_ratScalar (hRF : GlobalTheory.NT.RayField) {F : Face D A3.A} (fw : FWTie T Rl.toRealDat κ v₀) (hev : fw.Evaluates)
    (hcore : GlobalTheory.Hk3.Core Rl.toRealDat F) (hio : IoExt Rl.toRealDat) (hpb : T.pb = Rl.C.P.pb)
    (hnV : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) (hgal : IsGalois ℚ D.LL0) (hval : Formalism.L2.Host.ValLL0 D Rl.C)
    (hray : RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange)
    (hroots : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange)
    (hsp : D.host.cls D.host.pde = PrimeClass.splitK ∧ D.host.cls D.host.pde' = PrimeClass.splitK)
    {ρ : Setup D.ntw} (hρ : ρ.Good) (hpin : RealPin Rl cG ρ) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (hχ : ∀ p, (((ρ.B i j b).G.P.chi p : ℂˣ) : ℂ) ∈ (embLL0 D).fieldRange)
    (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j) {ν : ℂ} (hν : IsRatScalar T Rl κ v₀ hV (ρ.B i j b) ν)
    (s : Finset (Pl D.host.E)) (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank) :
    ρ.IsDatum i j b s h P → P ∈ ρ.lat i j b (GlobalTheory.BigOn.Exp.smallInt D) h →
      SmallComb YS v₀ j (ν • ρ.theta i j b h P) := by
  intro hd hPl
  have hti := tieIn_of_fw fw
  have hrd := readsAs_one YS fw hev hV
  obtain ⟨gR, cR, cL, -, u, hu, c, ph, -, -, rfl, hsc, hrat⟩ := hν
  have hT := hti.laws
  have hB := hρ.base i j b
  have hBo := baseOf_of_realPin hcore.lev hρ hpin i j b

  haveI := GlobalTheory.CoverSmall.smallF_normal D hgal
  obtain ⟨C, hpd, hfr, hC⟩ := exists_goodCover_pdAt YS hRF hT hti.alg hval hray hsp (D.ntw.l i) j (κ j).n
    (GlobalTheory.CoverSmall.smallF D) le_rfl
  have hLL : (embLL0 D).fieldRange ≤ C.σ₂.fieldRange := by
    rw [hfr]; exact fun z hz => hz
  have hLL' : C.σ₂.fieldRange ≤ (embLL0 D).fieldRange := by
    rw [hfr]; exact fun z hz => hz
  have hdat := isLevDatum_vecBase YS hT hcore hgal hval hroots hsp hρ hpin i j b hLL (fun p => hLL (hχ p))
    (fun x => hLL (delAt_mem Rl.C hval _ (hpin.delta i j b) x))
  rw [← hpd] at hdat
  have htw : IsTwist C.d.pd C.σ₂ (Rl.C.delAt (D.ntw.l i)) (ρ.B i j b).de.chi := by
    rw [hpd]; exact isTwist_delAt Rl.C hval _ (hpin.delta i j b) hLL
  have hω := hρ.weil_base i j b
  have hω' : IsWeilDatumO Rl.ψ (Vc D j) (Wc D j) (Lift.chrTh (Lift.tup Rl.mu0 (ρ.B i j b).de.chi) Rl.eta ((j : ℕ) + 1)).1
      (Lift.chrTh (Lift.tup Rl.mu0 (ρ.B i j b).de.chi) Rl.eta ((j : ℕ) + 1)).2 (ρ.om i j b 1) := by
    have h1 := hω
    rw [Base.IsWeil, mul_one, Base.mu, hBo.ψ, hBo.mu0, hBo.eta] at h1
    exact h1

  have hm : ∀ τ, (ρ.B i j b).w.p τ + (ρ.B i j b).w.q τ ≤ (Wc D j).rank := fun τ => by
    have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (tauE D τ)
    rw [← hB.sig τ] at h2
    exact h2.le
  have hinj := _root_.GlobalTheory.ExportSeries.HarmInj.harm_inj D _ _ (ρ.B i j b).w (ρ.B i j b).F.BS hB.wt hm
  refine smallComb_of_small ((ph * c) • (ρ.B i j b).theta (ρ.om i j b 1) h) hinj (fun G => ?_) (fun P hP G hPG => ?_) hPl
  · have h3 : coefFn (embLL0 D) (ρ.B i j b).w.lam (G : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) ∈
        (harm (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS).map (harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS) := by
      rw [GlobalTheory.T.fockHarmonicValueSpace_map_eq_dualWeylModuleFunctions D _ _ _ _ hB.wt hm]
      exact Submodule.subset_span ⟨GlobalTheory.CoefModel.mapVV (embLL0 D) _ G, (Scale.coefFn_map _ _ _).symm⟩
    exact h3
  · obtain ⟨G', hG', hPG'⟩ : ∃ G' : VV D.what₂.LL (FWT.lamV D j),
        (∀ m, D.what₂.embLL (AddMonoidAlgebra.coeff (G' : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) m) ∈ (embLL0 D).fieldRange) ∧
        harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P =
          coefFn D.what₂.embLL (FWT.lamV D j) (G' : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) := by
      rw [hPG]
      have hlam := hBo.lam
      generalize (ρ.B i j b).w.lam = lam at G hlam
      subst hlam
      refine ⟨⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV D.LL0.val.toRingHom _ _ G.2⟩, fun m => ⟨AddMonoidAlgebra.coeff G.1 m, ?_⟩, ?_⟩
      · exact congrArg D.what₂.embLL (MvPolynomial.coeff_map D.LL0.val.toRingHom G.1 m).symm
      · rw [← Scale.coefFn_map, ← Scale.coefFn_map D.what₂.embLL]
        exact congrArg _ (MvPolynomial.map_map _ _ _).symm
    have hP' := hsc.ioP_eq hinj hP (ioP_mem_valSpace hcore hio (hti.hv₀ j _) hB hBo hu _) hPG'
    have hR := ((hrat C hC hLL h hd.fin _ hdat (cL j G') (Submodule.subset_span ⟨G', fun m => hLL (hG' m), rfl⟩)).2 _ _ htw).2 _ hω'
    replace hR : IsRat T j hV C (κ j) ((ph * c) • (ρ.B i j b).theta (ρ.om i j b 1) h P) :=
      (congrArg (IsRat T j hV C (κ j)) (hpin.phase_mul_thetaKO i b hP' ph (ρ.om i j b 1) h (ρ.B i j b).vecBase)).mp hR
    obtain ⟨n, z, x, hz, e⟩ := exists_sum_evW YS hti hnV hcore.lev hpb hrd hC hR fun k hk g => by
      have := GlobalTheory.ExportType.theta_type hB (D.sp.V_sig _) hω (one_mem _) (lifts_one hBo hk) h P g
      rw [show (⟨1, one_mem _⟩ : (ρ.B i j b).G.P.H) = 1 from rfl, map_one, Units.val_one, one_mul] at this
      exact congrArg ((ph * c) * ·) this
    exact ⟨n, z, x, fun k => hLL' (hz k), by rw [LinearMap.smul_apply, e, one_smul]⟩

end Main

end GlobalTheory.SerSmall

end CorePart

section PointPart

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct

namespace GlobalTheory.SerSmall

section Core

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}

theorem exists_root_of_isNorm {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks)
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) {j : Fin D.R.m} (B : Base (Vc D j) (Wc D j)) {ν ν' : ℂ}
    (hN : IsNorm Rl v₀ B ν) (hN' : IsNorm Rl v₀ B ν') : ∃ ζ : ℂ, (∃ m : ℕ, m ≠ 0 ∧ ζ ^ m = 1) ∧ ν' = ζ * ν := by
  obtain ⟨h0, c, hc, n, hn, hνn⟩ := hN
  obtain ⟨-, c', hc', m, hm, hν'm⟩ := hN'
  obtain ⟨k, hk, hkk⟩ := isScale_pow_eq Rl v₀ _ hc hc'
  have e1 : ν' ^ (n * m * k) = (ν' ^ m) ^ (n * k) := by rw [← pow_mul]; ring_nf
  have e2 : ν ^ (n * m * k) = (ν ^ n) ^ (m * k) := by rw [← pow_mul]; ring_nf
  have e3 : c' ^ (n * m * k) = c ^ (n * m * k) := by
    rw [show n * m * k = k * (n * m) by ring, pow_mul c', pow_mul c, hkk]
  have e4 : ν' ^ (n * m * k) = ν ^ (n * m * k) := by
    rw [e1, e2, hν'm, hνn, ← pow_mul, ← pow_mul, mul_pow, mul_pow,
      show m * (n * k) = n * m * k by ring, show n * (m * k) = n * m * k by ring, e3]
  refine ⟨ν' / ν, ⟨_, Nat.mul_ne_zero (Nat.mul_ne_zero hn hm) hk, ?_⟩, (div_mul_cancel₀ ν' h0).symm⟩
  rw [div_pow, e4, div_self (pow_ne_zero _ h0)]

theorem smallComb_of_moved {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {Rl : RealDat3 D A3 Ks}
    {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
    (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → Γ) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (j : Fin D.R.m)
    {φ : GA D (Wc D j) → ℂ} (h : SmallComb (GlobalTheory.UnframeForms.movedYS YS w) v₀ j φ) : SmallComb YS v₀ j φ := by
  obtain ⟨n, z, g, hz, e⟩ := h
  refine ⟨n, z, fun k => (⟨(S.A ((j : ℕ) + 1)).ρ ((YS.fi j).eG.symm (w j (sg0 D A3.A)))
      (show ↥(S.A ((j : ℕ) + 1)).WK from g k).1,
    YS.rho _ (Nat.le_add_left _ _) j.2 _ _ (show ↥(S.A ((j : ℕ) + 1)).WK from g k).2⟩ : ↥(S.A ((j : ℕ) + 1)).WK), hz, ?_⟩
  rw [e]
  exact Finset.sum_congr rfl fun k _ => congrArg (z k • ·) (GlobalTheory.UnframeForms.evW_moved YS w v₀ j _)

theorem core_cases (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hRF : GlobalTheory.Published.RayClassFieldSt) (hS : GlobalTheory.SerStd.SeriesRatS)
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {Rl : RealDat3 D A3 T.Q.c.F} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
    {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) {F : Face D A3.A} {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)}
    {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
    {O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)} {ρ : Setup D.ntw} (hρ : ρ.Good) {i : D.ntw.Tw}
    {j : Fin D.R.m} (b : Bool) {hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j} (hpin : RealPin Rl cG ρ) (H : RatHyp T Rl F κ v₀ O i j hV)
    (hsp : D.host.cls D.host.pde = PrimeClass.splitK ∧ D.host.cls D.host.pde' = PrimeClass.splitK)
    (hχ : ∀ q, (((ρ.B i j b).G.P.chi q : ℂˣ) : ℂ) ∈ (Formalism.L2.Host.embLL0 D).fieldRange) :
    (∀ x ∈ (Rl.FW j).WK, x = 0) ∨ ∃ ν, IsNorm Rl v₀ (ρ.B i j b) ν ∧ ∀ s h P, ρ.IsDatum i j b s h P →
      P ∈ ρ.lat i j b (smallInt D) h → SmallComb YS v₀ j (ν • ρ.theta i j b h P) := by
  obtain ⟨fw⟩ := H.fw
  by_cases hc : T.toCore.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n = ⊥
  · refine Or.inl fun x hx => ?_
    obtain ⟨f, hf⟩ := (fw.e j).surjective ⟨x, hx⟩
    have h0 : f = 0 := Subtype.ext ((Submodule.eq_bot_iff _).1 hc f.1 f.2)
    rw [h0, map_zero] at hf
    exact (congrArg Subtype.val hf).symm
  · obtain ⟨ν, hN, hν⟩ := _root_.GlobalTheory.SeriesTie.NormRatStd.exists_isNorm_isRatScalar_std hA hRF hS D Γ Pl0 I0 T0 A3 T Rl cG S YS F κ v₀ O ρ hρ i j b hV hpin H hc
    exact Or.inr ⟨ν, hN, smallComb_of_ratScalar YS hRF fw (fw.evaluates_of_lUnif H.unif) H.core H.io
      (GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore Rl.toRealDat H.laws.toLawsM H.core.lev (H.pins.2.tuple ()).half)
      H.size H.galois H.small.val H.small.ray H.small.roots hsp hρ hpin i j b hχ hV hν⟩

end Core

section Level

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz}

theorem chi_mem_small (hm : RecTies p) {ρ : Setup D.ntw} (hρ : ρ.Good) (h : ρ.LevelOf D.nexp) (i : D.ntw.Tw) (j : Fin D.R.m)
    (b : Bool) (q : (ρ.B i j b).G.P.H) : (((ρ.B i j b).G.P.chi q : ℂˣ) : ℂ) ∈ (Formalism.L2.Host.embLL0 D).fieldRange := by
  obtain ⟨q, hq⟩ := q
  obtain ⟨g, rfl⟩ := (ρ.eG i j b).surjective q
  obtain ⟨u, rfl⟩ := (p.R.eG.trans p.cG).surjective g
  exact (level_chi hm hρ h i j b ⟨u, (mem_level_iff hm h i j b u).1 hq⟩ hq).2

end Level

open GlobalTheory.RealGeo GlobalTheory.Unframe GlobalTheory.UnframePt


end GlobalTheory.SerSmall

end PointPart
