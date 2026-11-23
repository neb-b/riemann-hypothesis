module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0862
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0798
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0878
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0947
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0961
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0976
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfClosedCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0946
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0916

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBirigidifiedBundleSymmetric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.HeckeSym

theorem grpSchemeSquareProductMap_comm_swap {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
    (ψ : A ⟶ A') :
    GlobalTheory.UPel.HT.Hecke.sq2 ψ ≫ (lift (snd A' A') (fst A' A')).left =
      (lift (snd A A) (fst A A)).left ≫ GlobalTheory.UPel.HT.Hecke.sq2 ψ := by
  unfold GlobalTheory.UPel.HT.Hecke.sq2
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  ext <;> simp

theorem descended_symm : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A') (G : Subgroup (𝟙_ (Over S) ⟶ o.A)), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover G (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∀ (m : ℕ) (P' : LB (G2 A').left), P'.IsLB → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → LBIso P' (P'.pull (lift (snd A' A') (fst A' A')).left) := by
  intro p _ D R _ b M S s o A' _ _ ψ G hA' hψ hG m P' hP' H r₁ r₂
  set sw' := (lift (snd A' A') (fst A' A')).left with hsw'
  set sw := (lift (snd o.A o.A) (fst o.A o.A)).left with hsw
  set q := GlobalTheory.UPel.HT.Hecke.sq2 ψ with hq
  have hQ : (P'.pull sw').IsLB := pull_isLB hP' sw'

  have ax : ∀ (e₁ e₂ : A' ⟶ G2 A'), e₁ ≫ lift (snd A' A') (fst A' A') = e₂ →
      (∃ t : (P'.pull e₂.left).Gen, t.IsGen) → ∃ t : ((P'.pull sw').pull e₁.left).Gen, t.IsGen := by
    intro e₁ e₂ he ⟨t, ht⟩
    have hc : ∀ k : PUnit, (fun _ : PUnit => e₁.left) k ≫ sw' = 𝟙 _ ≫ (fun _ : PUnit => e₂.left) k := by
      intro _
      rw [Category.id_comp, hsw', ← Over.comp_left, he]
    have iso : LBIso ((P'.pull sw').pull e₁.left) (P'.pull e₂.left) :=
      LBIso.chartPull (chartPullLinComb P' sw' (fun _ => e₁.left) (fun _ => e₂.left) (fun _ => 1) (𝟙 _) hc)
        (chartPullId _) (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hP' _))
    exact GlobalTheory.RigidTranslate.gen_of_lbIso (pull_isLB hP' _) (pull_isLB hQ _) iso.symm t ht
  have a₁ := ax (lift (1 : A' ⟶ A') (𝟙 A')) (lift (𝟙 A') (1 : A' ⟶ A')) (by ext <;> simp) r₂
  have a₂ := ax (lift (𝟙 A') (1 : A' ⟶ A')) (lift (1 : A' ⟶ A') (𝟙 A')) (by ext <;> simp) r₁

  have E := grpSchemeSquareProductMap_comm_swap ψ
  have hPow : (GlobalTheory.UPel.HT.Hecke.lbPow o.P m).IsLB := DVR.linComb_isLB _ o.isLB _ _
  have step1 : LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m)
      (LB.LinComb (o.P.pull sw) (K := Fin m) (fun _ => 𝟙 _) (fun _ => 1)) :=
    GlobalTheory.PowPrimitive.lbIso_linComb o.symm _ _
  have step2 : LBIso (LB.LinComb (o.P.pull sw) (K := Fin m) (fun _ => 𝟙 _) (fun _ => 1))
      ((P'.pull sw').pull q) := by
    refine LBIso.chartPull (h := sw)
      (chartPullLinComb o.P sw (fun _ => 𝟙 _) (fun _ => 𝟙 _) (fun _ => 1) sw (fun _ => by simp))
      (chartPullLinComb P' sw' (fun _ : PUnit => q) (fun _ : PUnit => q) (fun _ => 1) sw (fun _ => E)) H
  have hmid : (LB.LinComb (o.P.pull sw) (K := Fin m) (fun _ => 𝟙 _) (fun _ => 1)).IsLB :=
    DVR.linComb_isLB _ (pull_isLB o.isLB _) _ _
  have key : LBIso (P'.pull q) ((P'.pull sw').pull q) :=
    LBIso.trans (pull_isLB hP' q) hPow (pull_isLB hQ q) H.symm
      (LBIso.trans hPow hmid (pull_isLB hQ q) step1 step2)
  exact _root_.GlobalTheory.UPel.HT.Hecke.pullback_prod_injective_birigidified_galois_isogeny_alt S o.A A' G ψ o.ab hA' hψ hG P' (P'.pull sw') hP' hQ r₁ r₂ a₁ a₂ key

end GlobalTheory.HeckeSym
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvalueBarCompatibility
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjInner

theorem inner_eq_integral {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (e : H →ₗ[ℂ] MMap M) (c : ℂ)
    (h : ∀ x y, inner ℂ x y = c * ipM M μ 𝓕 (e x) (e y)) (v : M.Vec) (hv : ∀ τ, ‖(v τ : M.H τ)‖ = 1) (x y : H) :
    inner ℂ x y = c * ∫ g in 𝓕, star (e x v g) * e y v g ∂μ := by
  have hd : ∀ z : H, ∃ a, IsMultIP M μ 𝓕 (e z) (e z) a := by
    intro z
    by_cases hz : z = 0
    · refine ⟨0, fun v v' => ?_⟩
      subst hz
      simp
    · by_contra hn
      have := h z z
      simp only [ipM, dif_neg hn, mul_zero] at this
      exact hz (inner_self_eq_zero.1 this)
  obtain ⟨a, ha⟩ := hd x
  obtain ⟨b, hb⟩ := hd y
  obtain ⟨s, hs⟩ := hd (x + y)
  obtain ⟨t, ht⟩ := hd (x + Complex.I • y)
  rw [map_add (f := _)] at hs ht
  rw [map_smul] at ht
  have h1 := (ipM_spec M μ 𝓕 _ _ ⟨_, GlobalTheory.SchurPolar.exists_of_diag M μ 𝓕 _ _ ha hb hs ht⟩ v v).2
  rw [h, h1, Finset.prod_eq_one, mul_one]
  intro τ _
  rw [inner_self_eq_norm_sq_to_K, hv]
  simp

theorem conj_integral {X : Type} [MeasurableSpace X] (μ : Measure X) (q : ℂ) (hq : starRingEnd ℂ q = q) {a b a' b' : X → ℂ}
    (ha : ∀ g, a g = starRingEnd ℂ (a' g)) (hb : ∀ g, b g = starRingEnd ℂ (b' g)) :
    q * ∫ g, star (a g) * b g ∂μ = starRingEnd ℂ (q * ∫ g, star (a' g) * b' g ∂μ) := by
  rw [map_mul, hq, ← integral_conj]
  congr 2
  funext g
  rw [ha, hb, map_mul]
  rfl

theorem inner_conj_of_span {L W H H' : Type} [Field L] [AddCommGroup W] [Module L W] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : L →+* ℂ) (j : W →ₛₗ[σ] H)
    (j' : W →ₛₗ[(starRingEnd ℂ).comp σ] H') (s : Set W) (hs : Submodule.span L s = ⊤)
    (h : ∀ x ∈ s, ∀ y ∈ s, ⟪j x, j y⟫_ℂ = starRingEnd ℂ ⟪j' x, j' y⟫_ℂ) (x y : W) :
    ⟪j x, j y⟫_ℂ = starRingEnd ℂ ⟪j' x, j' y⟫_ℂ := by
  have hx : x ∈ Submodule.span L s := hs ▸ Submodule.mem_top
  have hy : y ∈ Submodule.span L s := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy => exact h x hx y hy
    | zero => simp
    | add y z _ _ h1 h2 => rw [map_add (f := _), map_add (f := _), inner_add_right, inner_add_right, map_add (f := _), h1, h2]
    | smul a y _ h1 =>
      rw [map_smulₛₗ, map_smulₛₗ, inner_smul_right, inner_smul_right, map_mul, h1, RingHom.comp_apply, Complex.conj_conj]
  | zero => simp
  | add x z _ _ h1 h2 => rw [map_add (f := _), map_add (f := _), inner_add_left, inner_add_left, map_add (f := _), h1, h2]
  | smul a x _ h1 =>
    rw [map_smulₛₗ, map_smulₛₗ, inner_smul_left, inner_smul_left, map_mul, h1, RingHom.comp_apply, Complex.conj_conj]

theorem dim_conj {D : D7} (W : HSp D) (σ : D.what₂.LL →+* ℂ) :
    (∏ ρ, ((dimK _ _ (kapAt W ((starRingEnd ℂ).comp σ) ρ) : ℚ) : ℂ)) = ∏ ρ, ((dimK _ _ (kapAt W σ ρ) : ℚ) : ℂ) := by
  refine Finset.prod_congr rfl fun ρ _ => ?_
  unfold kapAt
  rw [GlobalTheory.ConjEval.lab_conj]

theorem dim_real {D : D7} (W : HSp D) (σ : D.what₂.LL →+* ℂ) :
    starRingEnd ℂ (∏ ρ, ((dimK _ _ (kapAt W σ ρ) : ℚ) : ℂ)) = ∏ ρ, ((dimK _ _ (kapAt W σ ρ) : ℚ) : ℂ) := by
  rw [map_prod]
  exact Finset.prod_congr rfl fun ρ _ => map_ratCast _ _


set_option maxHeartbeats 1000000 in
theorem inner_conj_of_values {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (he : R.models_HW) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) {v : (R.MW i σ).Vec} {v' : (R.MW i ((starRingEnd ℂ).comp σ)).Vec} (hv : IsUnitV v) (hv' : IsUnitV v')
    {x y : (R.HW i σ).H} {x' y' : (R.HW i ((starRingEnd ℂ).comp σ)).H}
    (hx : ∀ g, evAt R i σ v x g = starRingEnd ℂ (evAt R i _ v' x' g))
    (hy : ∀ g, evAt R i σ v y g = starRingEnd ℂ (evAt R i _ v' y' g)) :
    ⟪x, y⟫_ℂ = starRingEnd ℂ ⟪x', y'⟫_ℂ := by
  have h1 := inner_eq_integral (R.MW i σ) (R.νW i) (R.fdW i) (R.HW i σ).e _ (he i σ).2.2 v hv x y
  have h2 := inner_eq_integral (R.MW i _) (R.νW i) (R.fdW i) (R.HW i _).e _ (he i _).2.2 v' hv' x' y'
  rw [dim_conj] at h2
  exact h1.trans ((conj_integral _ _ (dim_real _ σ) hx hy).trans (congrArg (starRingEnd ℂ) h2).symm)


end GlobalTheory.ConjInner
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvalueNormBound
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.StabFin

theorem norm_le_one_at_u : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (r : ℕ) (z : Gr G r) (K : Subgroup (Gr G r)) (g : Gr G r), 0 < r → Subgroup.Commensurable K (KHT p G.m G.n r G.Fw) → ∀ w : P.cent, P.toQr r z w ∈ K.map (MulAut.conj g).toMonoidHom → ∀ (a : FM P), jM P a = ((w : G.Cˣ × ℚˣ).1 : G.C) → ∀ τ : FM P →+* PadicAlgCl p, LiesOver G.Kq G.u (τ.comp (algebraMap G.F (FM P))) → ‖τ a‖ ≤ 1 := by
  intro p _ G P r z K g _ hK w hw a ha τ hτ
  obtain ⟨i, σ, hσ⟩ := G.emb_all _ hτ
  set τ' : FM P →+* PadicAlgCl p := ((σ.symm : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p).comp τ with hτ'
  have hτ'F : τ'.comp (algebraMap G.F (FM P)) = G.emb i := by
    rw [hτ', RingHom.comp_assoc, hσ]
    ext x; simp
  have hnorm : ‖τ a‖ = ‖τ' a‖ := by
    have : τ a = σ (τ' a) := by simp [hτ']
    rw [this]; exact (spectralNorm_eq_of_equiv σ _).symm
  rw [hnorm]
  obtain ⟨m, hm0, hm⟩ := exists_pow_mem_conj K (KHT p G.m G.n r G.Fw) g _ hK hw
  obtain ⟨k, hk, hkeq⟩ := hm
  obtain ⟨v, hv0, hv⟩ := GlobalTheory.T.exists_common_eigenvector_rho_adjoinRoot_embedding p G P i τ' hτ'F
  have hjm : jM P (a ^ m) = (((w ^ m : P.cent) : G.Cˣ × ℚˣ).1 : G.C) := by
    rw [map_pow, ha]; rfl
  have key : (z * g) * k * (z * g)⁻¹ = inclG G r (locC G ((w ^ m : P.cent) : G.Cˣ × ℚˣ)) := by
    have e : P.toQr r z (w ^ m) = z⁻¹ * inclG G r (locC G ((w ^ m : P.cent) : G.Cˣ × ℚˣ)) * z := rfl
    rw [map_pow] at e
    rw [← hkeq] at e
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at e
    have e2 : inclG G r (locC G ((w ^ m : P.cent) : G.Cˣ × ℚˣ)) =
        z * (z⁻¹ * inclG G r (locC G ((w ^ m : P.cent) : G.Cˣ × ℚˣ)) * z) * z⁻¹ := by group
    rw [e2, ← e]
    group
  have hcomp := congrArg (fun x : Gr G r => ((x.2 i : GL (Fin G.n) (KQ p (G.Fw i) r)) : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw i) r))) key
  have hk' : k.2 i ∈ Kres p (G.Fw i) G.n r := hk.2 i (Set.mem_univ _)
  have hb := GlobalTheory.T.eigenvalue_integral_norm_bound p (G.Fw i) G.n r (G.rho i (jM P (a ^ m))) ((z * g).2 i) (k.2 i) hk'
    (by rw [hjm]; exact hcomp.symm) v (τ' (a ^ m)) hv0 (hv _)
  rw [map_pow, norm_pow] at hb
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hm0.ne').1 hb

end GlobalTheory.StabFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfConjOnFinite
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjCharUnique

theorem eq_of_conj_on_finite {D : D7} {σ : D.what₂.LL →+* ℂ} {μ μ' μ'' : (AE D)ˣ →* Circle}
    (h1 : IsHeckeChar D μ') (g1 : IsHeckeChar D μ'')
    (h : ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ∃ y : D.what₂.LL,
      ((μ x : Circle) : ℂ) = D.what₂.embLL y ∧ ((μ' x : Circle) : ℂ) = σ y)
    (g : ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ∃ y : D.what₂.LL,
      ((μ x : Circle) : ℂ) = D.what₂.embLL y ∧ ((μ'' x : Circle) : ℂ) = σ y) : μ' = μ'' := by
  refine MonoidHom.ext fun x => mul_inv_eq_one.1 (GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite D (μ' * μ''⁻¹)
    ⟨h1.1.mul g1.1.inv, fun k => mul_inv_eq_one.2 ((h1.2 k).trans (g1.2 k).symm)⟩
    (fun y hy => mul_inv_eq_one.2 ?_) x)
  obtain ⟨a, ha, ha'⟩ := h y hy
  obtain ⟨b, hb, hb'⟩ := g y hy
  obtain rfl : a = b := D.what₂.embLL.injective (ha.symm.trans hb)
  exact Subtype.ext (ha'.trans hb'.symm)

end GlobalTheory.ConjCharUnique
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfNilpotentCommuteSeparableMinpoly
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx.ClsReg

theorem eq_zero_of_commute_of_pow_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (y₀ : G.C),
    (minpoly G.F y₀).Separable →
    (minpoly G.F y₀).natDegree = G.n → ∀ x : G.C, Commute x y₀ → ∀ k : ℕ, x ^ k = 0 → x = 0 := by
  intro p _ G y₀ hsep hdeg x hx k hk
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  ·
    have h10 : (1 : G.C) = 0 := by simpa using hk
    rw [← one_mul x, h10, zero_mul]
  have hk0 : k ≠ 0 := hkpos.ne'
  have hc := GlobalTheory.CentSep.centralizer_eq_adjoin G.F G.C G.n G.rankC y₀ hsep hdeg
  have hxmem : x ∈ Subalgebra.centralizer G.F ({y₀} : Set G.C) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.1 hg]
    exact hx.eq.symm
  rw [hc, Algebra.adjoin_singleton_eq_range_aeval] at hxmem
  obtain ⟨f, rfl⟩ := hxmem
  have h1 : Polynomial.aeval y₀ (f ^ k) = 0 := by
    rw [map_pow]; exact hk
  have h2 : minpoly G.F y₀ ∣ f ^ k := minpoly.dvd G.F y₀ h1
  have hsq : Squarefree (minpoly G.F y₀) := hsep.squarefree
  have h3 : minpoly G.F y₀ ∣ f := (hsq.dvd_pow_iff_dvd hk0).1 h2
  obtain ⟨g, hg⟩ := h3
  show Polynomial.aeval y₀ f = 0
  rw [hg, map_mul, minpoly.aeval, zero_mul]

end GlobalTheory.LKCx.ClsReg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinatesStalkFlat
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LogPair


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in
theorem _root_.GlobalTheory.LogPair.flat_germ_comp_cstOn_of_isEtCoord : ∀ {R : Type} [CommRing R] {Y : Scheme.{0}}
    (g : Y ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) (U : Y.Opens) {n : ℕ} (t : Fin n → Γ(Y, U)), IsAffineOpen U →
    _root_.GlobalTheory.LogPair.IsEtCoord g U t → ∀ (y : Y) (hy : y ∈ U),
    ((Y.presheaf.germ U y hy).hom.comp (_root_.GlobalTheory.LogPair.cstOn g U)).Flat := by
  intro R _ Y g U n t hU ht y hy
  have hC : (MvPolynomial.C : R →+* MvPolynomial (Fin n) R).Flat := by
    rw [← MvPolynomial.algebraMap_eq, RingHom.flat_algebraMap_iff]
    infer_instance
  have hE : (MvPolynomial.eval₂Hom (_root_.GlobalTheory.LogPair.cstOn g U) t).Flat := by
    have h : (MvPolynomial.eval₂Hom (_root_.GlobalTheory.LogPair.cstOn g U) t).Etale := ht
    letI := (MvPolynomial.eval₂Hom (_root_.GlobalTheory.LogPair.cstOn g U) t).toAlgebra
    have : Algebra.Etale (MvPolynomial (Fin n) R) Γ(Y, U) := h
    show Module.Flat _ _
    infer_instance
  have hG : (Y.presheaf.germ U y hy).hom.Flat := by
    letI := (Y.presheaf.germ U y hy).hom.toAlgebra
    have := hU.isLocalization_stalk ⟨y, hy⟩
    show Module.Flat _ _
    exact IsLocalization.flat _ (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
  rw [← MvPolynomial.eval₂Hom_comp_C (_root_.GlobalTheory.LogPair.cstOn g U) t, ← RingHom.comp_assoc]
  exact (hC.comp hE).comp hG

end GlobalTheory.LogPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfClosedCoverStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleHomotopyInvariantTwists_of_closedCover : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (I J : Ideal A), I ⊓ J ≤ nilradical A → IsUnit (q : A) → HInv q (A ⧸ I) → HInv q (A ⧸ J) → HInv q (A ⧸ (I ⊔ J)) → HInv q A := by
  first | (exact @GlobalTheory.EtC.ClosedCover.closedCover) | (exact GlobalTheory.EtC.ClosedCover.closedCover) | (intros; apply GlobalTheory.EtC.ClosedCover.closedCover  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralConjOfIntegralConjGeneratorStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_integral_conj_of_integral_conj_generator : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (γ : G.Cˣ), (minpoly G.F (γ : G.C)).natDegree = G.n →
    ∀ (L : Type) [Field L] [NumberField L] (ι : L →ₐ[ℚ] G.C), Function.Injective ι →
    (∀ z : G.C, z * γ = γ * z ↔ ∃ w, ι w = z) → ∀ (κ : Type) (b : Module.Basis κ ℚ G.C)
    (κ' : Type) (ℓ : Module.Basis κ' ℚ L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ X : (v.adicCompletion ℚ ⊗[ℚ] G.C)ˣ,
      IsIntB v b (↑X * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (γ : G.C)) * ↑X⁻¹) →
      ∀ ρ, IsIntB v ℓ ρ →
        IsIntB v b (↑X * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι ρ * ↑X⁻¹) := by
  first | (exact @GlobalTheory.ConjInt.isIntB_conj_map_of_isIntB_conj) | (exact GlobalTheory.ConjInt.isIntB_conj_map_of_isIntB_conj) | (intros; apply GlobalTheory.ConjInt.isIntB_conj_map_of_isIntB_conj  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralCoordsScalarTensorInclusion
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.FinClsLoc
open IsDedekindDomain

theorem ratAdicInt_eventually (q : ℚ) :
    ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite,
      algebraMap ℚ (v.adicCompletion ℚ) q ∈ v.adicCompletionIntegers ℚ := by
  have h := (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q).2
  filter_upwards [h] with v hv
  exact hv

theorem intC_inC_eventually : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (c : G.C), ∀ᶠ w : AwayP p in Filter.cofinite,
    IntC G w (inC G (w.1.adicCompletion ℚ) c) := by
  intro p _ G c
  have hall : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ i : Fin (Module.finrank ℚ G.C),
      algebraMap ℚ (v.adicCompletion ℚ) ((Module.finBasis ℚ G.C).repr c i) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun i => ratAdicInt_eventually _
  have ht : Filter.Tendsto (Subtype.val : AwayP p → HeightOneSpectrum ℤ) Filter.cofinite Filter.cofinite :=
    Subtype.val_injective.tendsto_cofinite
  filter_upwards [ht.eventually hall] with w hw
  intro i
  have : coordL G w (inC G (w.1.adicCompletion ℚ) c) i =
      algebraMap ℚ (w.1.adicCompletion ℚ) ((Module.finBasis ℚ G.C).repr c i) := by
    have e : inC G (w.1.adicCompletion ℚ) c = (1 : w.1.adicCompletion ℚ) ⊗ₜ[ℚ] c := rfl
    rw [coordL, e, Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]
  rw [this]; exact hw i

end GlobalTheory.FinClsLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralMatrixUnitsAtPlacesStatement
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_integral_matrix_units_at_places : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∃ E : Fin G.n → Fin G.n → Qv v ⊗[ℚ] G.C, (∀ i j k l, E i j * E k l = if j = k then E i l else 0) ∧ ∑ i, E i i = 1 ∧ ∀ i j, IsIntV G v (E i j) := by
  first | (exact @GlobalTheory.OrbFinAf.MatrixUnits₂.matrixUnits_eventually) | (exact GlobalTheory.OrbFinAf.MatrixUnits₂.matrixUnits_eventually) | (intros; apply GlobalTheory.OrbFinAf.MatrixUnits₂.matrixUnits_eventually  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIsIntegralOfIntegralCoordsLocalTensor
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.FinClsLoc

open IsDedekindDomain

theorem eventually_rat_mem_adicCompletionIntegers (q : ℚ) :
    ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite,
      algebraMap ℚ (v.adicCompletion ℚ) q ∈ v.adicCompletionIntegers ℚ := by
  have h := (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q).2
  filter_upwards [h] with v hv
  exact hv

theorem intC_isIntegral : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), ∀ᶠ w : AwayP p in Filter.cofinite,
    ∀ x : w.1.adicCompletion ℚ ⊗[ℚ] G.C, IntC G w x → (∃ f : Polynomial (w.1.adicCompletion ℚ), f.Monic ∧
      (∀ i, f.coeff i ∈ w.1.adicCompletionIntegers ℚ) ∧ Polynomial.aeval x f = 0) := by
  intro p _ G
  set b := Module.finBasis ℚ G.C with hb
  have hev : ∀ᶠ w : AwayP p in Filter.cofinite, ∀ k j l,
      algebraMap ℚ (w.1.adicCompletion ℚ) (b.repr (b k * b j) l) ∈ w.1.adicCompletionIntegers ℚ := by
    rw [Filter.eventually_all]; intro k
    rw [Filter.eventually_all]; intro j
    rw [Filter.eventually_all]; intro l
    exact Subtype.val_injective.tendsto_cofinite.eventually (eventually_rat_mem_adicCompletionIntegers _)
  filter_upwards [hev] with w hw
  intro x hx
  set B := Algebra.TensorProduct.basis (w.1.adicCompletion ℚ) b with hB
  have hent : ∀ i j, Algebra.leftMulMatrix B x i j ∈ w.1.adicCompletionIntegers ℚ := by
    intro i j
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    rw [← B.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_mul, map_sum, Finsupp.finsetSum_apply]
    refine sum_mem fun k _ => ?_
    rw [smul_mul_assoc, map_smul, Finsupp.smul_apply, smul_eq_mul]
    have e : B k * B j = (1 : w.1.adicCompletion ℚ) ⊗ₜ[ℚ] (b k * b j) := by
      simp [hB, Algebra.TensorProduct.basis_apply]
    rw [e, Algebra.TensorProduct.basis_repr_tmul]
    simp only [one_smul, Finsupp.mapRange_apply]
    exact mul_mem (hx k) (hw k j i)
  refine ⟨(Algebra.leftMulMatrix B x).charpoly, Matrix.charpoly_monic _, ?_, ?_⟩
  · intro n
    let M : Matrix (Fin (Module.finrank ℚ G.C)) (Fin (Module.finrank ℚ G.C)) (w.1.adicCompletionIntegers ℚ) :=
      fun i j => ⟨_, hent i j⟩
    have hM : Algebra.leftMulMatrix B x = M.map (algebraMap (w.1.adicCompletionIntegers ℚ) (w.1.adicCompletion ℚ)) := by
      ext i j; rfl
    rw [hM, Matrix.charpoly_map, Polynomial.coeff_map]
    exact (M.charpoly.coeff n).2
  · apply Algebra.leftMulMatrix_injective B
    rw [← Polynomial.aeval_algHom_apply, Matrix.aeval_self_charpoly, map_zero]

end GlobalTheory.FinClsLoc
end
end

