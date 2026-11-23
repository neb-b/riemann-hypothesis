module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2746
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2755
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2764
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2789
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2793
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0598
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1685
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1664
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1518
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1745
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2790
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2788
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1981
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2795
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2267
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2208
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1733
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2799
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMixedLagrangianChartIntegralRowChange

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtDualOfConn
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.Dieu.EtFromConn

namespace GlobalTheory.Dieu.EtFromConn

variable {p : ℕ} [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn))

section Main

theorem exists_unique_isTr {k k' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k']
    [CharP k' p] [PerfectRing k' p] {σ : k →+* k'} {G' : PDivGroup p k'} {G : PDivGroup p k}
    (hG' : G'.IsEt) (hG : G.IsEt) (s : SemiHom σ G' G) (l : Mod B G hG) :
    ∃! l', IsTr B σ hG' hG s l l' := by
  letI : Algebra k k' := σ.toAlgebra
  have hb := (_root_.GlobalTheory.Dieu.baseChange_isConn_isEt p k k' G.dual).1 (dual_conn hG)
  obtain ⟨l', h1, h2⟩ := _root_.GlobalTheory.semiHom_dual_transpose p B k k' G G' (dual_conn hG) (dual_conn hG') hb s l
  exact ⟨l', ⟨hb, h1⟩, fun l'' ⟨_, h⟩ => h2 l'' h⟩

theorem isTr_tr {k k' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k']
    [CharP k' p] [PerfectRing k' p] {σ : k →+* k'} {G' : PDivGroup p k'} {G : PDivGroup p k}
    (hG' : G'.IsEt) (hG : G.IsEt) (s : SemiHom σ G' G) (l : Mod B G hG) :
    IsTr B σ hG' hG s l (tr B hG' hG s l) :=
  tr_spec B hG' hG s l (exists_unique_isTr B hG' hG s l).exists

theorem tr_eq {k k' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k']
    [CharP k' p] [PerfectRing k' p] {σ : k →+* k'} {G' : PDivGroup p k'} {G : PDivGroup p k}
    (hG' : G'.IsEt) (hG : G.IsEt) (s : SemiHom σ G' G) (l : Mod B G hG) (l' : Mod B G' hG')
    (h : IsTr B σ hG' hG s l l') : tr B hG' hG s l = l' :=
  (exists_unique_isTr B hG' hG s l).unique (isTr_tr B hG' hG s l) h

theorem tr_add {k k' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k']
    [CharP k' p] [PerfectRing k' p] {σ : k →+* k'} {G' : PDivGroup p k'} {G : PDivGroup p k}
    (hG' : G'.IsEt) (hG : G.IsEt) (s : SemiHom σ G' G) (l m : Mod B G hG) :
    tr B hG' hG s (l + m) = tr B hG' hG s l + tr B hG' hG s m := by
  apply tr_eq
  have h1 := isTr_tr B hG' hG s l
  have h2 := isTr_tr B hG' hG s m
  letI : Algebra k k' := σ.toAlgebra
  obtain ⟨hb, lb, a1, b1⟩ := h1
  obtain ⟨_, mb, a2, b2⟩ := h2
  refine ⟨hb, lb + mb, fun x => ?_, fun y => ?_⟩
  · rw [LinearMap.add_apply, a1, a2, LinearMap.add_apply, map_add (f := _)]
  · rw [LinearMap.add_apply, b1, b2, LinearMap.add_apply]

theorem tr_smul {k k' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k']
    [CharP k' p] [PerfectRing k' p] {σ : k →+* k'} {G' : PDivGroup p k'} {G : PDivGroup p k}
    (hG' : G'.IsEt) (hG : G.IsEt) (s : SemiHom σ G' G) (a : WittVector p k) (l : Mod B G hG) :
    tr B hG' hG s (a • l) = WittVector.map σ a • tr B hG' hG s l := by
  apply tr_eq
  have h1 := isTr_tr B hG' hG s l
  letI : Algebra k k' := σ.toAlgebra
  obtain ⟨hb, lb, a1, b1⟩ := h1
  refine ⟨hb, WittVector.map σ a • lb, fun x => ?_, fun y => ?_⟩
  · rw [LinearMap.smul_apply, a1, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, map_mul]
  · rw [LinearMap.smul_apply, b1, LinearMap.smul_apply]

theorem tr_ofHom {k : Type} [Field k] [CharP k p] [PerfectRing k p] {G H : PDivGroup p k}
    (hG : G.IsEt) (hH : H.IsEt) (f : G ⟶ H) (l : Mod B H hH) :
    tr B hG hH (SemiHom.ofHom f) l = l ∘ₗ B.map (dual_conn hH) (dual_conn hG) (dualHom G H f) :=
  tr_eq B hG hH _ l _ (_root_.GlobalTheory.Dieu.EtFromConn.isTr_ofHom p B k G H hG hH f l)

def etBase : Base p (fun _ _ G => G.IsEt) where
  M G h := ModuleCat.of (WittVector p _) (Mod B G h)
  smap h' h s :=
    { toFun := tr B h' h s
      map_zero' := by simpa using tr_smul B h' h s 0 0
      map_add' := tr_add B h' h s }
  red G h := red B G h
  free G h := by
    haveI := B.free G.dual (dual_conn h)
    haveI := B.finite G.dual (dual_conn h)
    change Module.Free (WittVector p _) (Module.Dual _ (B.M G.dual (dual_conn h)))
    infer_instance
  finite G h := by
    haveI := B.free G.dual (dual_conn h)
    haveI := B.finite G.dual (dual_conn h)
    change Module.Finite (WittVector p _) (Module.Dual _ (B.M G.dual (dual_conn h)))
    infer_instance
  red_surjective G h := by
    have hb := PDivGroup.rigToLie_bijective_and_dual_rigOfOmega_bijective_of_isEt p _ (p_eq_zero p _) G h
    exact (rigLie G h).symm.surjective.comp
      ((LinearMap.dualMap_surjective_of_injective hb.2.1).comp (redDual_spec B G h).2.1)
  red_eq_zero G h m := by
    have hb := PDivGroup.rigToLie_bijective_and_dual_rigOfOmega_bijective_of_isEt p _ (p_eq_zero p _) G h
    change (rigLie G h).symm _ = 0 ↔ _
    rw [LinearEquiv.map_eq_zero_iff, ← map_zero G.dual.rigOfOmega.dualMap, LinearMap.comp_apply,
      (LinearMap.dualMap_injective_of_surjective hb.2.2).eq_iff]
    exact (redDual_spec B G h).2.2 m
  smap_smul h' h s a m := tr_smul B h' h s a m
  smap_id G h m := by
    change tr B h h _ m = m
    rw [tr_ofHom]
    refine LinearMap.ext fun y => ?_
    rw [LinearMap.comp_apply, dualHom_id]
    exact congrArg m (B.smap_id _ _ y)
  smap_add hG hH f g m := by
    change tr B hG hH _ m = tr B hG hH _ m + tr B hG hH _ m
    rw [tr_ofHom, tr_ofHom, tr_ofHom]
    refine LinearMap.ext fun y => ?_
    rw [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, ← map_add m,
      map_add (dualHom _ _)]
    exact congrArg m (B.smap_add _ _ _ _ y)
  smap_comp h'' h' h s t u hu m :=
    (tr_eq B h'' h u m _ (_root_.GlobalTheory.Dieu.EtFromConn.isTr_comp p B _ _ _ _ _ _ _ _ _ h'' h' h s t u hu m _ _
      (isTr_tr B h' h s m) (isTr_tr B h'' h' t _)))
  red_smap h' h s m := GlobalTheory.T.etaleDieudonneTranspose_eq_rigidifiedExtensionPullback p B _ _ _ _ _ h' h s m _ (isTr_tr B h' h s m)

end Main

end GlobalTheory.Dieu.EtFromConn

namespace GlobalTheory.Dieu

theorem exists_etDual_of_conn : ∀ (p : ℕ) [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn)),
    ∃ C : Base p (fun _ _ G => G.IsEt), C.EtDual B := by
  intro p _ B
  refine ⟨EtFromConn.etBase B, fun G h hd hG => LinearEquiv.refl _ _, fun G h hd hG => ⟨?_, ?_⟩⟩
  · intro x y
    exact _root_.GlobalTheory.Dieu.EtFromConn.isTr_absFrob_F p B _ G h x _ (EtFromConn.isTr_tr B h h _ x) y
  · intro H h' hd' hH f x y
    exact LinearMap.congr_fun (EtFromConn.tr_ofHom B h h' f x) y

end GlobalTheory.Dieu
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalSeriesOfCoboundaryDvdP
section
set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog


set_option maxHeartbeats 1000000 in
theorem exists_series_of_cobOne_dvd : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (b : G.A 1) (z : G.A 1 ⊗[O] G.A 1), cobOne O (G.A 1) b = (p : O) • z → ∃ (κ : MvPowerSeries (Fin d ⊕ Fin d) O) (B : MvPowerSeries (Fin d) O) (y : G.A 1), constantCoeff κ = 0 ∧ (∀ α, (p : O) ∣ coeff α (cob2 c.μ κ)) ∧ (∀ α, (p : O) ∣ coeff α (Katz.swap κ - κ)) ∧ (∀ α, (p : O) ∣ coeff α (cob1 c.μ B - pull2 (nmul c.μ p) κ)) ∧ c.ev 1 B = b + (p : O) • y := by
  intro p _ O _ G d c b z hbz
  let I : Ideal O := Ideal.span {(p : O)}
  have hpI : (p : O) ^ 1 ∈ I := by rw [pow_one]; exact Ideal.subset_span rfl
  obtain ⟨c', hlaw, hev, -⟩ := _root_.GlobalTheory.QLog.ChartRed.exists_chart p O G d c I 1 hpI
  have hmkp : (algebraMap O (O ⧸ I)) (p : O) = 0 := by
    rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.subset_span rfl
  have hb' : cobOne (O ⧸ I) ((G.baseChange (O ⧸ I)).A 1) ((G.toBase (O ⧸ I)).app 1 b) = 0 := by
    rw [← SemiBialgHom.two_cobOne, hbz, map_smulₛₗ, hmkp, zero_smul]
  obtain ⟨κ', B', hcoc, hκ0, hcob, hev1⟩ := _root_.GlobalTheory.Katz.Chart.exists_series_of_cobOne_eq_zero p (O ⧸ I) d _ c' _ hlaw _ hb'
  obtain ⟨hl2, hz2, -⟩ := GlobalTheory.mvPowerSeries_lift_quotient O (Fin d ⊕ Fin d) I
  obtain ⟨hl1, hz1, -⟩ := GlobalTheory.mvPowerSeries_lift_quotient O (Fin d ⊕ (Fin d ⊕ Fin d)) I
  obtain ⟨hl0, -, -⟩ := GlobalTheory.mvPowerSeries_lift_quotient O (Fin d) I
  obtain ⟨κ, hκ, hκc⟩ := hl2 κ'
  obtain ⟨B, hB, -⟩ := hl0 B'
  have hdiv : ∀ x : O, x ∈ I ↔ (p : O) ∣ x := fun x => Ideal.mem_span_singleton
  have hμ := c.isLaw.const
  obtain ⟨hm1, hm2, hsw, -, hpull⟩ := _root_.GlobalTheory.Katz.map_cob_swap_pull O d c.μ hμ (O ⧸ I) (Ideal.Quotient.mk I)
  obtain ⟨-, hn⟩ := _root_.GlobalTheory.isLaw_map_nmul O d c.μ c.isLaw (O ⧸ I) (Ideal.Quotient.mk I)
  have hnm : (fun i => map (Ideal.Quotient.mk I) (nmul c.μ p i)) =
      nmul (fun i => map (Ideal.Quotient.mk I) (c.μ i)) p := funext fun i => (hn p i).2
  obtain ⟨hpl, -⟩ := hpull (nmul c.μ p) fun i => (hn p i).1
  have hy : ∃ y : G.A 1, c.ev 1 B = b + (p : O) • y := by
    have h1 : (G.toBase (O ⧸ I)).app 1 (c.ev 1 B) = (G.toBase (O ⧸ I)).app 1 b := by
      rw [← hev, hB, hev1]
    rw [toBase_app, toBase_app] at h1
    have h2 : (1 : O ⧸ I) ⊗ₜ[O] (c.ev 1 B - b) = 0 := by rw [tmul_sub, h1, sub_self]
    obtain ⟨-, hq, hs⟩ := GlobalTheory.PDiv.one_tmul_quot_reduction O (G.A 1) I
    obtain ⟨y, hy⟩ := (hs (p : O) _).1 ((hq _).1 h2)
    exact ⟨y, by rw [← hy]; abel⟩
  obtain ⟨y, hy⟩ := hy
  refine ⟨κ, B, y, hκc hκ0, ?_, ?_, ?_, hy⟩
  · intro α
    refine (hdiv _).1 ((hz1 _).1 ?_ α)
    rw [hm2, hκ]; exact hcoc.1
  · intro α
    refine (hdiv _).1 ((hz2 _).1 ?_ α)
    rw [map_sub, hsw, hκ, hcoc.2, sub_self]
  · intro α
    refine (hdiv _).1 ((hz2 _).1 ?_ α)
    rw [map_sub, hm1, hpl, hκ, hB, hnm, hcob, sub_self]

end GlobalTheory.QLog
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsBottomOfIsCoprime
section
noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.SqNum

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}

theorem exists_isBottom_of_isCoprime (hL : L.Is μ₀) (G : GridData L sc)
    (hm : IsCoprime (condE G.pl) D.host.𝔟) (hm' : IsCoprime (D.host.conj • condE G.pl) D.host.𝔟) :
    ∃ δ t0 : ℂ, ∀ i j : Fin D.R.m, ∃ P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 (levQ G.pl),
      IsBottom G μ₀ i j (condE G.pl) P P' := by
  obtain ⟨δ, hδ⟩ := GlobalTheory.NormSum.exists_crv_top D
  obtain ⟨t0, ht⟩ := (GlobalTheory.TwoTorsionPt.exists_point D ⊤ δ hδ).1
  refine ⟨δ, t0, fun i j => ?_⟩
  obtain ⟨χν, hν, hw⟩ := GlobalTheory.BottomNu.exists_heckeU_nu_inv hL G i j
  obtain ⟨χβ, hβ⟩ := exists_betaInv_heckeU hL G i j
  obtain ⟨χα, hα⟩ := exists_heckeU_alphaH hL G i j
  obtain ⟨P, h1, h2, h3, h4, h5⟩ := _root_.GlobalTheory.FunObj.StdDatum.exists_bottom_big hL G hm hδ ht i j χβ hβ χν hν hw
  obtain ⟨P', h1', h2', h3', h4', h5'⟩ := _root_.GlobalTheory.BotPairSmall.smallPair_exists hL G hm' hδ ht i j χα hα χν hν hw
  exact ⟨P, P', ⟨⟨h1, h1', h2, h2'.trans h2.symm⟩, h3, h3', h4, h4', ⟨h5, h5'⟩⟩⟩

theorem exists_isBottom (hL : L.Is μ₀) (G : GridData L sc) (hq : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) :
    ∃ δ t0 : ℂ, ∀ i j : Fin D.R.m, ∃ P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 (levQ G.pl),
      IsBottom G μ₀ i j (condE G.pl) P P' :=
  exists_isBottom_of_isCoprime hL G (GlobalTheory.FunObj.StdDatum.HalfDiff.condE_isCoprime_halfDifferent G.pl hq).1
    (GlobalTheory.FunObj.StdDatum.HalfDiff.condE_isCoprime_halfDifferent G.pl hq).2

end GlobalTheory.FunObj.SqNum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelledUniformisedModelThetaSystemTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem traitLabels : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (ε : Matrix (Fin 8) (Fin 8) ℤ → (ρ.P.A ⟶ ρ.P.A)) (u' : Sp S.R ⟶ F.X), IsDiagEnd F W ρ.P u' ε → ∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (T : Trait F) (ι : FractionRing T.V →+* PadicAlgCl p), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) → spMap y₀ ≫ u' = spMap ι ≫ T.y → (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∃ (u : ρ.UTest p y₀) (l : u.Lab) (j : u.D.toPre.X ≃+ (Fin 8 → T.D.toPre.X)), (∀ χ, l.q χ = -Real.log ‖ι (algebraMap T.V (FractionRing T.V) T.ϖ)‖ * ((qW W T.β (j χ) : ℤ) : ℝ)) ∧ ∀ (m : ℕ) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (E : Matrix (Fin 8) (Fin 8) ℤ), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → x'.left ≫ u.φ = x.left ≫ u.φ ≫ (ε E).left → CongMod m (j pk'.y) (fun a => ∑ b, E a b • j pk.y b) := by
  intro g n F W hW o Ω _ _ _ _ S ρ ε u' hD p _ y₀ T ι hι hsp hint
  obtain ⟨T', ι', yK, e, k, hι', hfac, hy', hϖ, hβ⟩ := _root_.GlobalTheory.TraitExtLab.main g n F o Ω S u' p y₀ T ι hι hsp
  obtain ⟨A, φ, cart, lb, εA, hDA, huniq⟩ := _root_.GlobalTheory.Poinc.DiagPull.exists_pull_field g n F W S.R ρ.P ε u' hD (FractionRing T'.V) yK
  rw [hy'] at hDA
  obtain ⟨G', _, _, hsemi, D', U', j', hpsi, hcong⟩ := GlobalTheory.T.eighthPower_trait_uniformisation_lattice_pow_eight g n F W hW T' A εA hDA
  letI : Algebra (FractionRing T'.V) (PadicAlgCl p) := ι'.toAlgebra
  let u : ρ.UTest p y₀ := { V := T'.V, complete := T'.complete, norm_le := hι', yK := yK, fac := hfac, A := A, φ := φ, cart := cart, lb := lb, G := G', semi := hsemi, D := D', U := U' }
  obtain ⟨l⟩ := GlobalTheory.ZH.labels_exist GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 GlobalTheory.ZH.uTors_closed o Ω S ρ p y₀ u hint
  let jj : u.D.toPre.X ≃+ (Fin 8 → T.D.toPre.X) := j'.trans (AddEquiv.piCongrRight fun _ => e)
  refine ⟨u, l, jj, ?_, ?_⟩
  · intro χ

    obtain ⟨v, hv⟩ := hpsi χ
    obtain ⟨jc, hjc, hval⟩ := _root_.GlobalTheory.Poinc.valF_psi_of_psiCoord T'.V D'.toPre χ _ hv
    have hq := l.q_eq χ jc hjc
    change ‖algebraMap (FractionRing T'.V) (PadicAlgCl p) (valF (𝟙 (Sp (FractionRing T'.V))) _ ((D'.toPre.psi χ).s jc).val)‖ = _ at hq
    rw [hval, RingHom.algebraMap_toAlgebra] at hq

    have hunit : ‖ι' (algebraMap T'.V _ (v : T'.V))‖ = 1 := by
      have h1 : ‖ι' (algebraMap T'.V _ (v : T'.V))‖ ≤ 1 := (hι' _).2 ⟨_, rfl⟩
      have h2 : ‖ι' (algebraMap T'.V _ ((v⁻¹ : T'.Vˣ) : T'.V))‖ ≤ 1 := (hι' _).2 ⟨_, rfl⟩
      have h3 : ‖ι' (algebraMap T'.V _ (v : T'.V))‖ * ‖ι' (algebraMap T'.V _ ((v⁻¹ : T'.Vˣ) : T'.V))‖ = 1 := by
        rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
      nlinarith [norm_nonneg (ι' (algebraMap T'.V _ (v : T'.V))), norm_nonneg (ι' (algebraMap T'.V _ ((v⁻¹ : T'.Vˣ) : T'.V)))]
    set a := ‖ι' (algebraMap T'.V _ T'.ϖ)‖ with ha
    have hq0 : 0 ≤ qW W T'.β (j' χ) :=
      qW_nonneg_of_posW W hW.1 T'.β T'.symm (GlobalTheory.Poinc.Basic₂.trait_nonneg T') (j' χ)
    have hsc : qW W T'.β (j' χ) = (k : ℤ) * qW W T.β (jj χ) := by
      simp only [qW, hβ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      simp only [jj, AddEquiv.trans_apply, AddEquiv.piCongrRight_apply]
      ring
    rw [map_mul, map_mul, norm_mul, hunit, one_mul, map_pow, map_pow, norm_pow] at hq
    rw [← ha] at hq
    have hN : ((qW W T'.β (j' χ)).toNat : ℝ) = ((k : ℤ) : ℝ) * (qW W T.β (jj χ) : ℝ) := by
      rw [← Int.cast_mul, ← hsc]
      exact_mod_cast Int.toNat_of_nonneg hq0
    have hapos : 0 < a := by
      rw [ha, norm_pos_iff]
      intro h0
      have : algebraMap T'.V (FractionRing T'.V) T'.ϖ = 0 := ι'.injective (by rw [h0, map_zero])
      exact T'.irr.ne_zero (IsFractionRing.injective T'.V (FractionRing T'.V) (by rw [this, map_zero]))
    have hl : -l.q χ = ((qW W T'.β (j' χ)).toNat : ℝ) * Real.log a := by
      rw [← Real.log_pow, hq, Real.log_exp]
    rw [hϖ, Real.log_pow]
    rw [hN] at hl
    push_cast at hl ⊢
    linarith
  · intro m pk pk' x x' E hm h1 h2 hx
    have hc := hcong (PadicAlgCl p) m pk pk' x x' E hm h1 h2 (huniq _ x x' E hx)
    obtain ⟨w, hw⟩ := hc
    refine ⟨fun a => e (w a), ?_⟩
    funext a
    have := congrFun hw a
    simp only [jj, AddEquiv.trans_apply, AddEquiv.piCongrRight_apply, Pi.add_apply, Pi.smul_apply, Finset.sum_apply] at this ⊢
    set_option synthInstance.maxHeartbeats 100000 in
      rw [this, map_add (f := _), map_sum, map_nsmul]
    simp [map_zsmul]

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMixedChartThroughWCoordinate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

noncomputable section

namespace GlobalTheory.TopFlip.ChartA

open GlobalTheory.FlipMatch.RowChart GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (blk)

theorem tr_full {k : Type} [Field k] {n p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) {b β g : GL (Fin n) k}
    {Gm : Matrix (Fin n) (Fin n) k} (hg : g.val = -(β.valᵀ * Gmᵀ * b.val))
    {c cc : GL (Fin d) k} {βV : GL (Fin p) k} {β₁ : GL (Fin q) k} (hC : c.val * cc.val = blk e βV.val (-β₁.val))
    (U : Matrix (Fin n) (Fin d) k) :
    g.val * ((b⁻¹).val * U * (c⁻¹).valᵀ) * (invT cc).val =
      (blk e (βV⁻¹).val (-(β₁⁻¹).val) * (Uᵀ * -Gm) * β.val)ᵀ := by
  have h : g.val * ((b⁻¹).val * U * (c⁻¹).valᵀ) * (invT cc).val =
      (-(β.valᵀ * Gmᵀ) * U) * blk e (βV⁻¹).valᵀ (-(β₁⁻¹).valᵀ) := by
    rw [← inv_of_blk e hC, invT_val, hg]
    simp only [Matrix.neg_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc b.val, Units.mul_inv, Matrix.one_mul]
  rw [h]
  simp only [transpose_mul, transpose_neg, transpose_transpose, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc,
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_transpose]

theorem map_frame {A R k : Type} [CommRing A] [CommRing R] [Field k] (f : A →+* R) (c : R →+* k) {n p q d : ℕ}
    (e : Fin p ⊕ Fin q ≃ Fin d) (β : GL (Fin n) R) (βV : GL (Fin p) R) (β₁ : GL (Fin q) R)
    (J : Matrix (Fin n) (Fin n) A) (u : Matrix (Fin n) (Fin d) A) :
    (((GlobalTheory.Doubling.blkGL finSumFinEquiv (βV, -β₁))⁻¹).val *
        (uᵀ.submatrix (e.symm.trans finSumFinEquiv).symm id * J).map f * β.val).map c =
      (blk e ((GeneralLinearGroup.map c βV)⁻¹).val (-((GeneralLinearGroup.map c β₁)⁻¹).val) *
        ((u.map (c.comp f))ᵀ * J.map (c.comp f)) * (GeneralLinearGroup.map c β).val).submatrix
        (e.symm.trans finSumFinEquiv).symm id := by
  have h1 : (((GlobalTheory.Doubling.blkGL finSumFinEquiv (βV, -β₁))⁻¹).val).map c =
      (blk e ((GeneralLinearGroup.map c βV)⁻¹).val (-((GeneralLinearGroup.map c β₁)⁻¹).val)).submatrix
        (e.symm.trans finSumFinEquiv).symm (e.symm.trans finSumFinEquiv).symm := by
    have h0 : ((GlobalTheory.Doubling.blkGL finSumFinEquiv (βV, -β₁))⁻¹).val =
        GlobalTheory.Doubling.blkMat finSumFinEquiv (βV⁻¹).val (-(β₁⁻¹).val) := rfl
    rw [h0, GlobalTheory.Doubling.blkMat_map _ _ (map_zero c), Matrix.map_neg _ (map_neg c)]
    ext a b
    simp only [GlobalTheory.Doubling.blkMat, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, submatrix_apply, reindex_apply, Equiv.symm_trans_apply, Equiv.symm_symm,
      Equiv.symm_apply_apply]
    rfl
  rw [Matrix.map_mul, Matrix.map_mul, h1, Matrix.map_mul, Matrix.map_mul]
  have h2 : ((uᵀ.submatrix (e.symm.trans finSumFinEquiv).symm id).map f).map c * (J.map f).map c =
      ((u.map (c.comp f))ᵀ * J.map (c.comp f)).submatrix (e.symm.trans finSumFinEquiv).symm id := rfl
  rw [h2, submatrix_mul_equiv]
  rfl

section Grid

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} (B : Frames G) (t : T)
  (i j : Fin D.R.m) (e : Num G i j)

theorem linA_ptA (w : Pl D.host.E)
    (u : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :
    linA B t i j w (ptA e u) = reindex (finCongr (rankW G t i j w)) (colsEq t e w)
      (blk e ((loc w (B.β i (j + 1)))⁻¹).val (-((loc w (B.β (i + 1) j))⁻¹).val) *
        HMul.hMul (u.map (cw w))ᵀ (-(spW G i j).gram.map (algebraMap D.host.E (Kw w))) *
        (loc w (B.β (i + 1) (j + 1))).val)ᵀ := by
  have eJ : (incM (GlobalTheory.Grid.sgn true (spW G i j)).gram).map (cw w) =
      -(spW G i j).gram.map (algebraMap D.host.E (Kw w)) :=
    Matrix.ext fun a b => (Good.cpt_incA _ _).trans (map_neg (algebraMap D.host.E (Kw w)) _)
  have k2 := map_frame (toEAf D) (cpt (D := D) w) (n := (spW G i j).rank) e (B.β (i + 1) (j + 1)) (B.β i (j + 1))
    (B.β (i + 1) j) (incM (GlobalTheory.Grid.sgn true (spW G i j)).gram) u
  rw [← eJ]
  refine Matrix.ext fun r s => ?_
  refine (congrFun (congrFun k2 ((colX G t i j w).symm s)) ((finCongr (rankW G t i j w)).symm r)).trans ?_
  have hs : (e.symm.trans finSumFinEquiv).symm ((colX G t i j w).symm s) = (colsEq t e w).symm s :=
    congrArg e (finSumFinEquiv.symm_apply_apply _)
  rw [submatrix_apply, hs]
  rfl

theorem chart_eq_linA (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) {v : Pl D.host.F}
    (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (w : Pl D.host.E) (ψ : Fv D.host.F v ≃+* Kw w) (hjj : IsPlaceIso τ w ψ)
    (cc : GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Kw w))
    (hcc : (Γ.W.bas v).val.map ψ * cc.val = basCols B e w) (g : GL (Fin (spW G i j).rank) (Kw w))
    (hg : g.val = -((loc w (B.β (i + 1) (j + 1))).valᵀ *
      ((spW G i j).gram.map (algebraMap D.host.E (Kw w)))ᵀ * (Γ.V.bas v).val.map ψ))
    (u : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :
    chart ψ (finCongr (rankW G t i j w)) (colsEq t e w) g (invT cc) (coX τ (Γ.V.bas v) (Γ.W.bas v) u) =
      linA B t i j w (ptA e u) := by
  have eU : (u.map (piW τ)).map ψ = u.map (cw w) := Matrix.ext fun a b => hjj _
  have k1 := tr_full e (b := GeneralLinearGroup.map ψ.toRingHom (Γ.V.bas v))
    (c := GeneralLinearGroup.map ψ.toRingHom (Γ.W.bas v)) (β := loc w (B.β (i + 1) (j + 1)))
    (βV := loc w (B.β i (j + 1))) (β₁ := loc w (B.β (i + 1) j)) hg hcc (u.map (cw w))
  rw [linA_ptA, chart, chart_coX, eU]
  exact congrArg _ k1

end Grid

theorem exists_mixChart_lin : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G), SquareStanding G t →
    ∀ (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
      (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' → IsTied t i j e Bs Γ X →
    ∀ (v : Bs.P) (w : Pl D.host.E), splitPrime (Bs.τ v) = w → ∀ jj : Fv D.host.F v ≃+* Kw w, IsPlaceIso (Bs.τ v) w jj → IsLocIso jj →
    ∀ cc : GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Kw w), (Γ.W.bas v).val.map jj * cc.val = basCols B e w →
    ∃ g ∈ KO (Kw w) (Fin (spW G i j).rank),
      IsMixChart v.1 (mixHalf e (atPl w 1)) (mixHalf e (cA D (atPl w 1))) (mixCo B t e w)
        (fun u => chart jj (finCongr (rankW G t i j w)) (colsEq t e w) g (invT cc) (coX (Bs.τ v) (Γ.V.bas v) (Γ.W.bas v) u))
        (fun u => (xiAt w)⁻¹ • chart jj (finCongr (rankW G t i j w)) (colsEq t e w) (invT g) cc
          (coY D.sp.cm.sig Γ.V Γ.W (Bs.τ v) (Γ.V.bas v) (Γ.W.bas v) u))
        (Assignment.one.block _ _)ᶜ ∧
      ∀ u, chart jj (finCongr (rankW G t i j w)) (colsEq t e w) g (invT cc) (coX (Bs.τ v) (Γ.V.bas v) (Γ.W.bas v) u) =
        linA B t i j w (ptA e u) := by
  classical
  intro D T L sc G μ₀ hL W B t i j M _ e Bs Γ X om om' h hT hTi v w hw jj hjj _ cc hcc
  subst hw
  obtain rfl := eq_complEquiv _ hjj
  have hV := hT.geo.hV
  have hJT : IsHermND D.sp.cm.sig Γ.V.Jᵀ := ⟨fun i j => by simpa using hV.herm j i, by
    rw [Matrix.det_transpose]; exact GlobalTheory.HermSelfDualLoc.det_ne_zero_of_isHerm _ Bs hV⟩
  have hsd := GlobalTheory.HermSelfDualLoc.isSelfDualAt_transpose _ _ _ Bs _ Γ.V _ _ hT.base hV v
  have hb := hV.bas v
  rw [hTi.1] at hsd hb
  obtain ⟨g, hgK, hg⟩ := exists_rows (Bs.τ v) hJT hsd hb
    (isFrameAt_loc (B.isFrame_β hL (i := (i : ℕ) + 1) (j := (j : ℕ) + 1) i.2 j.2) (splitPrime (Bs.τ v)))
  have hJW : Γ.V.J = (spW G i j).gram := h.JW.trans (one_smul _ _)
  rw [hJW] at hg
  refine ⟨g, hgK, isMixChart_of B t i j e Γ (Bs.τ v) _ hjj (complMap_apply_emb _ _) hJW h.JWW cc hcc g hg, fun u => ?_⟩
  exact chart_eq_linA B t i j e Γ (Bs.τ v) _ _ hjj cc hcc g hg u

end GlobalTheory.TopFlip.ChartA

end
end

