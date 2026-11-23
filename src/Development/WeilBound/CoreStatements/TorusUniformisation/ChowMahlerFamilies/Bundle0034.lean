module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0070
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.SplitMultiplicativeHopfOrder
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0023
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TestOrderSections
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0033
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0032
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsDualFamily
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0003
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IsUnitOfVal
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ValCastSub
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1045
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0085

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TestGroupPointExists
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.TestGroupPoint

theorem spanOver_ind {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o C] [Algebra Ω C] (RC : Subalgebra o C)
    {r : ℕ} (L : AddSubgroup (Fin r → Ω)) (T : AddSubgroup (Fin r → C)) (hT : ∀ t ∈ RC, ∀ a ∈ T, t • a ∈ T)
    (h : ∀ a ∈ L, (fun k => algebraMap Ω C (a k)) ∈ T) : spanOver RC (bcMap Ω C _ '' L) ≤ T := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨t, ht, _, ⟨a, ha, rfl⟩, rfl⟩
  exact hT t ht _ (h a ha)

theorem mem_spanOver {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o C] [Algebra Ω C] (RC : Subalgebra o C)
    {r : ℕ} (L : AddSubgroup (Fin r → Ω)) {a : Fin r → Ω} (ha : a ∈ L) :
    (fun k => algebraMap Ω C (a k)) ∈ spanOver RC (bcMap Ω C _ '' L) :=
  AddSubgroup.subset_closure ⟨1, RC.one_mem, _, ⟨a, ha, rfl⟩, (one_smul _ _).symm⟩

def smallSub {C : Type} [Field C] (v : Valuation C NNReal) (t : NNReal) {r : ℕ} {I : Type}
    (f : I → ((Fin r → C) →ₗ[C] C)) : AddSubgroup (Fin r → C) where
  carrier := {a | ∀ m, v (f m a) ≤ t}
  add_mem' ha hb m := by rw [map_add (f := _)]; exact v.map_add_le (ha m) (hb m)
  zero_mem' m := by simp
  neg_mem' ha m := by rw [map_neg, Valuation.map_neg]; exact ha m

theorem bar_bar {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (a : 𝓞 E) : H.bar (H.bar a) = a :=
  RingOfIntegers.ext (by rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply])

end PositivityTheory.Xgn.TestGroupPoint

open PositivityTheory.Xgn.TestGroupPoint PositivityTheory.HtPt.Sgp in
theorem PositivityTheory.Xgn.test_group_point_exists : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → GlobalTheory.CompanionTheory.Ar.GR.QuotientByFiniteFlatStatement → GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement → GlobalTheory.CompanionTheory.Ar.GR.HodgeTateDatumStatement → GlobalTheory.CompanionTheory.Ar.GR.OrdinaryCurveStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ [DecidableEq F] [Fintype (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)] [DecidableEq (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)], ∀ (v : Valuation C NNReal), (∀ c, c ∈ RC ↔ v c ≤ 1) → v (p : C) < 1 → ∀ τ (hb : ((Fin (labelRk D (e τ)) → C) →ₗ[C] (Fin (D.p + D.q) → C))), Function.Injective hb → LinearMap.range hb = LinearMap.ker (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))) → (stdLat RC _).comap hb.toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).W τ → (∀ a ∈ ((chartD e b pq sc w P i).bc RC).W τ, hb a - GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (i τ) a ∈ mulLat (algebraMap O C w) (stdLat RC _)) → (((chartD e b pq sc w P i).bc RC).hh RC p (fun a => χ τ a)).map (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))).toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).om τ ∧ (((chartD e b pq sc w P i).bc RC).hh RC p (fun a => χ τ a)).comap hb.toAddMonoidHom = divLat (algebraMap O C w) (((chartD e b pq sc w P i).bc RC).lie τ) := by
  intro hF _ _ hHD hOC E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hd hpq p _ hpS hfree hp2 hdisc b hb φ hφ A _ _ _ m _
    hpm O _ _ _ _ _ _ _ t₀ Sg _ e φ' F _ _ _ pq sc w σF hO hsec G c' hc' P i hseq hbase C _ _ _ _ RC hT χ hχ _ _ _ v hv hvp
    τ hbm _ _ hW hcl
  have hpp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hpp.ne_zero⟩
  haveI : NeZero (p ^ 𝔐.R p) := ⟨pow_ne_zero _ hpp.ne_zero⟩
  have hR4 := 𝔐.R_ge p hpS
  obtain ⟨h0, hNoe, hIC, hFr⟩ := Par.chart_facts E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd p hpS A m hpm O c' hc'
  obtain ⟨-, hN, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HT.hcpt_generic_point E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS (Par.zp Ω p) (Par.mem_range_zp Ω p)
  obtain ⟨AA, AW, hAA, hAW, hM, hret, -⟩ := PositivityTheory.Xgn.test_order_sections E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd hpq p
    hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σF hO hsec G c' hc' P i hseq hbase C RC hT χ hχ
  obtain ⟨-, htight⟩ := _root_.PositivityTheory.Xgn.tight_hopf_order_test hHD hOC E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd hpq p
    hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σF hO hsec G c' hc' P i hseq hbase C RC hT χ hχ v hv hvp
  obtain ⟨g, io, ev, Hm, Eg, hio, hev, hcard, hEt, ⟨Ei, hEi, hiso⟩, hE, hH⟩ :=
    point_data hF E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd hpq p hpS A m hpm O G c' hc' P C RC w hO.2.2.2.2.2.2.2 hT
  obtain ⟨Dv, hD, hDs, hDch⟩ := exists_der hpS P hT.2.2.2 io
  have hlat := fun t => lattices E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd hpq p hpS A m hpm O G c' hc' P C RC hdisc
    hT.2.2.2 io ev hio hev t (b t) (hb t).1 (hb t).2
  haveI := hT.1
  haveI : CharZero C := charZero_of_injective_algebraMap (algebraMap Ω C).injective
  have hint : v.Integers RC := ⟨Subtype.val_injective, fun x => (hv _).1 x.2, fun r hr => ⟨⟨r, (hv _).2 hr⟩, rfl⟩⟩
  obtain ⟨φN, hφN⟩ := exists_phiN E (D.p + D.q) p
  have hζ : IsPrimitiveRoot (algebraMap Ω C (G.ζ ^ p ^ (𝔐.R p - 1))) p :=
    (G.ζ_prim.pow (pow_pos hpp.pos _) (by rw [← pow_succ, Nat.sub_add_cancel (by omega)])).map_of_injective
      (algebraMap Ω C).injective
  let ih : (Fin (D.p + D.q) → 𝓞 E) →+ (Fin g → RC) := io.toAddMonoidHom.comp (P.Dh.h.codRestrict P.Dh.om P.Dh.h_mem)
  obtain ⟨cp, hcp, k0, k1, k2, k3, k4⟩ := core_pull hint hvp hp2 φN hφN AA _ hAA htight hcard
    (dvd_pow_self p (show 𝔐.R p ≠ 0 by omega)) G.e hζ (kernel_mem hpS P hT) Dv hD (Set.range io) hio
    (by rintro _ ⟨u, rfl⟩; exact hDs u) ih hDch Hm Eg Ei hEt hEi hiso hE hH
  obtain ⟨σ, hσ, hσs, -⟩ := PositivityTheory.Xgn.exists_cm_type_embedding E H D l Xo c O₀ β Y S Ω K J y 𝔐 (e τ)
  obtain ⟨hσO, x₀, hx₀, o₀, ho₀⟩ := PositivityTheory.Xgn.SequenceDifferentials.main E Ω p hdisc A m hpm O σ
  have hOC' : ∀ o : O, algebraMap Ω C (algebraMap O Ω o) = algebraMap O C o := fun o =>
    (IsScalarTower.algebraMap_apply O Ω C o).symm
  obtain ⟨σ', s, hσ', hs, hdu⟩ := exists_dualOf (R := RC) (C := C) Subtype.val_injective ((algebraMap Ω C).comp σ)
    (fun a => by
      obtain ⟨o, ho⟩ := hσO a
      exact ⟨algebraMap O RC o, by rw [RingHom.comp_apply, ← ho, hOC']; rfl⟩)
    (fun k => by
      obtain ⟨z, hz⟩ := HT.exists_different_mul_dualInt E x₀ hx₀ k
      obtain ⟨o, ho⟩ := hσO z
      refine ⟨algebraMap O RC (o₀ * o), ?_⟩
      have : algebraMap O Ω (o₀ * o) = σ (HT.dualInt E k) := by
        rw [map_mul, ho, hz, map_mul, ← _root_.mul_assoc, ho₀, _root_.one_mul]
      rw [RingHom.comp_apply, ← this, hOC']; rfl)
  obtain ⟨χ', hχ', hcong⟩ := chi_cong p RC v hv pq sc hsec (σF τ) (χ τ) (hχ τ) σ' fun a => by
    obtain ⟨o, ho, ho'⟩ := hO.2.2.2.2.1 τ a
    exact ⟨o, by rw [← hOC', ho, ← hσ]; exact (hσ' a).symm, ho'⟩
  have hst := afLat_stable hdu φN hφN AA.carrier (fun a f hf => by rw [hAA] at hf ⊢; exact act_mem P a f hf) _
    (mem_pull φN AA)
  have hhh := (pt_af_type_main RC p (ReciprocityTheory.PGsh.Up.hopfPull φN AA).carrier (ReciprocityTheory.PGsh.Up.hopfPull φN AA).le_int
    ((chartD e b pq sc w P i).bc RC) χ' (Subtype.ext (by rw [← hχ', map_zero]; rfl))
    (Subtype.ext (by rw [← hχ', map_one]; rfl))
    (φN.symm.toAddMonoidHom.comp (TestPt.toNAdd sc)) ((TestPt.fromNAdd pq).comp φN.toAddMonoidHom)
    (fun z => by
      change TestPt.fromNAdd pq (φN (φN.symm (TestPt.toNAdd sc z))) = z
      rw [AddEquiv.apply_symm_apply]
      exact funext fun k => hsec.1 (z k))
    (fun h hh => by
      obtain ⟨f, hf, rfl⟩ := (mem_pull φN AA h).1 hh
      refine (mem_pull φN AA _).2 ⟨_, hret f hf, funext fun x => ?_⟩
      change _ = f (φN (φN.symm _))
      rw [AddEquiv.apply_symm_apply]
      rfl)
    (by
      rw [← hM, hAW, TestPt.testOrdW, ← hAA]
      congr 1
      ext f
      constructor
      · rintro ⟨h, hh, rfl⟩
        obtain ⟨f, hf, rfl⟩ := (mem_pull φN AA h).1 hh
        refine ⟨f, hf, funext fun x => ?_⟩
        change _ = f (φN (φN.symm _))
        rw [AddEquiv.apply_symm_apply]
        rfl
      · rintro ⟨f, hf, rfl⟩
        refine ⟨_, (mem_pull φN AA _).2 ⟨f, hf, rfl⟩, funext fun x => ?_⟩
        change f (φN (φN.symm _)) = _
        rw [AddEquiv.apply_symm_apply]
        rfl)
    (Pm _ σ') (Jm _ s) (Pm_mul_Jm hdu) (Pm_cong pq φN hφN χ' hcong) hst).2
  simp only [← hχ'] at hhh
  obtain ⟨u, hu, hwu⟩ := hO.2.2.2.2.2.2.1.2.1
  have hp3 : 2 ≤ p - 1 := by have := hpp.two_le; omega
  have hvw : v (algebraMap O C w) ^ (p - 1) = v (p : C) := by
    rw [← map_pow, ← map_pow, hwu, map_mul, map_mul, map_natCast,
      show v (algebraMap O C u) = 1 from hint.one_of_isUnit (hu.map (algebraMap O RC)), _root_.one_mul]
  have hw1 : v (algebraMap O C w) < 1 := lt_of_not_ge fun h => absurd (hvw ▸ one_le_pow₀ h) (not_le.2 hvp)
  have hw0 : algebraMap O C w ≠ 0 := fun h => by
    rw [h, map_zero, zero_pow (by omega), eq_comm, Valuation.zero_iff] at hvw
    exact Nat.cast_ne_zero.2 hpp.ne_zero hvw
  have hpw : v (p : C) ≤ v (algebraMap O C w) * v (algebraMap O C w) := by
    rw [← hvw, ← sq]
    exact pow_le_pow_of_le_one zero_le hw1.le hp3
  have hWl : ∀ a ∈ ((chartD e b pq sc w P i).bc RC).W τ, algebraMap O C w • a ∈ ((chartD e b pq sc w P i).bc RC).lie τ :=
    fun a ha => spanOver_ind RC _ (divLat (algebraMap O C w) (((chartD e b pq sc w P i).bc RC).lie τ))
      (fun t ht a ha => by
        simp only [divLat, AddSubgroup.mem_comap, DistribSMul.toAddMonoidHom_apply] at ha ⊢
        rw [smul_comm]
        exact smul_mem_spanOver RC _ ht ha)
      (fun a ha => by
        have h1 : algebraMap O Ω w • a ∈ (chartD e b pq sc w P i).lie τ := (hbase.incl τ).2.1 ha
        have h2 := mem_spanOver RC _ h1
        have e : algebraMap O C w • (fun k => algebraMap Ω C (a k)) =
            fun k => algebraMap Ω C ((algebraMap O Ω w • a) k) := by
          funext k
          change _ = algebraMap Ω C (algebraMap O Ω w * a k)
          rw [map_mul, hOC']
          rfl
        simp only [divLat, AddSubgroup.mem_comap, DistribSMul.toAddMonoidHom_apply]
        rw [e]
        exact h2) ha
  have heig : ∀ t a k, 𝔐.ρ a (b t k) = 𝔐.emb t a • b t k := fun t a k => by
    have : b t k ∈ 𝔐.Vgen t := (hb t).2 ▸ Submodule.subset_span ⟨k, rfl⟩
    simp only [HodgeCpt.Vgen, GlobalTheory.CompanionTheory.Ar.eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      sub_eq_zero] at this
    exact this a
  refine typed RC v hv (p : C) (algebraMap O C w) hw0 hw1 hpw cp (p : RC)
    ((pow_left_inj₀ zero_le zero_le (by omega)).1 (hcp.trans hvw.symm)) (SubringClass.coe_natCast _ _) _ Hm Eg Ei hEi
    k0 k1 k2 k3 k4 (Pm _ σ') (Jm _ s) (Pm_mul_Jm hdu) hst _ hhh (fun k => ev (b (e τ).swap k)) (fun k => ev (b (e τ) k))
    _ _ _ (hlat (e τ).swap).1 (hlat (e τ)).2
    (spanOver_ind RC _ _ (fun t ht a ha => smul_mem_spanOver RC _ ht ha) fun a ha =>
      mem_spanOver RC _ ((hbase.incl τ).1 ha)) hWl _
    (hq_chart P.Dh 𝔐.ρ H.bar io ev Hm (by omega) P.Dh_act hev hH σ σ' hσ' (b (e τ).swap) fun a k => ?_)
    (TestPt.bcLin C (i τ)) hbm (fun a ha => ?_) hW hcl
  · rw [heig, ← hσs, H.bar_eq, RingHom.comp_apply]
    congr 2
    first
      | exact IsCMField.complexConj_apply_apply E _
      | simp [HT.cmConj]
  · let f : Ix E (D.p + D.q) → ((Fin (labelRk D (e τ)) → C) →ₗ[C] C) := fun m =>
      ∑ m', (Eg m m' : C) • (LinearMap.proj m' ∘ₗ ((Jm _ s).map (algebraMap RC C)).mulVecLin ∘ₗ TestPt.bcLin C (i τ)) +
        ∑ k, ev (b (e τ) k) (fun j => (Hm j m : C)) • LinearMap.proj k
    have hf : ∀ m a, f m a = ∑ m', (Eg m m' : C) * ((Jm _ s).map (algebraMap RC C)).mulVec (TestPt.bcLin C (i τ) a) m' +
        ∑ k, a k * ev (b (e τ) k) fun j => (Hm j m : C) := fun m a => by
      simp only [f, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
        LinearMap.proj_apply, Matrix.mulVecLin_apply, smul_eq_mul, mul_comm (a _)]
    intro m
    rw [← hf]
    refine spanOver_ind RC _ (smallSub v (v (algebraMap O C w)) f) (fun t ht a ha m => ?_) (fun a ha m => ?_) ha m
    · rw [map_smul, smul_eq_mul, map_mul]
      exact (mul_le_of_le_one_left zero_le ((hv _).1 ht)).trans (ha m)
    · rw [hf, show TestPt.bcLin C (i τ) (fun k => algebraMap Ω C (a k)) = fun l => algebraMap Ω C (i τ a l) from
        funext (bcLin_bc _ _)]
      exact hdual_chart P.Dh 𝔐.ρ H.bar io ev Hm (by omega) P.Dh_act hev hH (bar_bar H)
        (by rw [P.Dh_e]; exact G.adj) Eg (by rw [P.Dh_e]; exact hE) σ σ' hσ' s hs hdu (b (e τ))
        (fun a k => by rw [heig, hσ]) v hv _ hw0 hw1.le hpw a (i τ a)
        (fun l => (hseq τ).1.1 a ha l (Set.mem_univ l)) (M := 𝔐.R p - 2) (by omega) ((hseq τ).2 σ hσ a ha)
        ((hlat (e τ)).2 _ |>.1 (hWl _ (mem_spanOver RC _ ha))) m
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XXgzHeightRVolUpModelMat
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

namespace PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_mat

theorem exists_ext (K : Type) [Field K] [NumberField K] (τ : 𝓞 K →+* ℂ) :
    ∃ σ : K →+* ℂ, σ.comp (algebraMap (𝓞 K) K) = τ := by
  have hinj : Function.Injective τ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    have h : Function.Injective (τ.comp (algebraMap ℤ (𝓞 K))) := RingHom.injective_int _
    rw [RingHom.injective_iff_ker_eq_bot] at h
    exact (RingHom.comap_ker τ (algebraMap ℤ (𝓞 K))).trans h
  refine ⟨IsFractionRing.lift (A := 𝓞 K) (K := K) (L := ℂ) (g := τ) hinj, ?_⟩
  ext x
  exact IsFractionRing.lift_algebraMap (K := K) hinj x

theorem ext_unique (K : Type) [Field K] [NumberField K] {σ σ' : K →+* ℂ}
    (h : σ.comp (algebraMap (𝓞 K) K) = σ'.comp (algebraMap (𝓞 K) K)) : σ = σ' :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 K)) h

theorem unitary_of_norm {N : ℕ} (W : Matrix (Fin N) (Fin N) ℂ)
    (h : ∀ y : Fin N → ℂ, Real.sqrt (∑ i, ‖W.mulVec y i‖ ^ 2) = Real.sqrt (∑ i, ‖y i‖ ^ 2)) :
    W ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  have h1 : ∀ y : EuclideanSpace ℂ (Fin N), ‖Matrix.toEuclideanLin W y‖ = ‖y‖ := fun y => by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    exact h y.ofLp
  have h2 := (LinearMap.norm_map_iff_inner_map_map (Matrix.toEuclideanLin W)).1 h1
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  have := h2 (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  rw [EuclideanSpace.inner_single_left] at this
  simp only [PiLp.inner_apply] at this
  simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.toEuclideanLin, mul_comm, eq_comm] using this

theorem exists_unitary {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ) (hA : A.det ≠ 0) (hB : B.det ≠ 0)
    (h : ∀ x : Fin N → ℂ, GlobalTheory.ChowHt.frameNorm B (fun j => (starRingEnd ℂ) (x j)) = GlobalTheory.ChowHt.frameNorm A x) :
    ∃ U ∈ Matrix.unitaryGroup (Fin N) ℂ, B = A.map (starRingEnd ℂ) * U := by
  have hW : B⁻¹ * A.map (starRingEnd ℂ) ∈ Matrix.unitaryGroup (Fin N) ℂ := by
    refine unitary_of_norm _ fun y => ?_
    have := h (A.mulVec fun j => (starRingEnd ℂ) (y j))
    unfold GlobalTheory.ChowHt.frameNorm at this
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA.isUnit, Matrix.one_mulVec] at this
    have e : (fun j => (starRingEnd ℂ) (A.mulVec (fun j => (starRingEnd ℂ) (y j)) j)) =
        (A.map (starRingEnd ℂ)).mulVec y := by
      funext j
      simp [Matrix.mulVec, dotProduct]
    rw [e, Matrix.mulVec_mulVec] at this
    simpa using this
  refine ⟨star (B⁻¹ * A.map (starRingEnd ℂ)), Unitary.star_mem hW, ?_⟩
  have h1 := Matrix.mem_unitaryGroup_iff.1 hW
  calc B = B * ((B⁻¹ * A.map (starRingEnd ℂ)) * star (B⁻¹ * A.map (starRingEnd ℂ))) := by rw [h1, mul_one]
    _ = _ := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB.isUnit, Matrix.one_mul]

theorem exists_P {K : Type} [Field K] {N m : ℕ} (g : Matrix (Fin N) (Fin m) K)
    (hg : Submodule.span K (Set.range g.col) = ⊤) :
    ∃ (r : ℕ) (e : Fin m ≃ Fin N ⊕ Fin r) (P : Matrix (Fin m) (Fin m) K), P.det ≠ 0 ∧
      g * P = (Matrix.fromCols (1 : Matrix (Fin N) (Fin N) K) (0 : Matrix (Fin N) (Fin r) K)).submatrix id e := by
  have hs : LinearMap.range g.mulVecLin = ⊤ := by
    rw [Matrix.range_mulVecLin]; exact hg
  obtain ⟨s, hs'⟩ := LinearMap.exists_rightInverse_of_surjective _ hs
  have hs2 : ∀ x, g.mulVecLin (s x) = x := fun x => LinearMap.congr_fun hs' x
  set r := Module.finrank K (LinearMap.ker g.mulVecLin) with hr
  have hdim : N + r = m := by
    have := LinearMap.finrank_range_add_finrank_ker g.mulVecLin
    rw [hs, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at this
    exact this
  let e : Fin m ≃ Fin N ⊕ Fin r := (finCongr hdim.symm).trans finSumFinEquiv.symm
  let c : (Fin r → K) ≃ₗ[K] LinearMap.ker g.mulVecLin := (Module.finBasis K _).equivFun.symm
  let φ : (Fin m → K) →ₗ[K] (Fin m → K) :=
    s ∘ₗ LinearMap.funLeft K K (fun i => e.symm (Sum.inl i)) +
      (LinearMap.ker g.mulVecLin).subtype ∘ₗ c.toLinearMap ∘ₗ LinearMap.funLeft K K (fun i => e.symm (Sum.inr i))
  have hφ : ∀ v, φ v = s (fun i => v (e.symm (Sum.inl i))) + (c (fun i => v (e.symm (Sum.inr i))) : Fin m → K) :=
    fun v => rfl
  have hgφ : ∀ v, g.mulVecLin (φ v) = fun i => v (e.symm (Sum.inl i)) := fun v => by
    rw [hφ, map_add (f := _), hs2, LinearMap.mem_ker.1 (c _).2, add_zero]
  refine ⟨r, e, LinearMap.toMatrix' φ, ?_, ?_⟩
  · intro h0
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    rw [LinearMap.toMatrix'_mulVec] at hv0
    have h1 : (fun i => v (e.symm (Sum.inl i))) = 0 := by rw [← hgφ, hv0, map_zero]
    have h2 : (fun i => v (e.symm (Sum.inr i))) = 0 := by
      rw [hφ, h1, map_zero, zero_add] at hv0
      exact c.map_eq_zero_iff.1 (Subtype.ext hv0)
    refine hv (funext fun a => ?_)
    obtain ⟨a, rfl⟩ := e.symm.surjective a
    rcases a with i | i
    · exact congrFun h1 i
    · exact congrFun h2 i
  · ext j a
    have := congrFun (hgφ (Pi.single a 1)) j
    rw [Matrix.mulVecLin_apply, ← LinearMap.toMatrix'_mulVec φ, Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at this
    rw [show (g * LinearMap.toMatrix' φ) j a = _ from this]
    obtain ⟨a, rfl⟩ := e.symm.surjective a
    rcases a with i | i <;> simp [Pi.single_apply, Matrix.one_apply]

end PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_mat

theorem PositivityTheory.Xgn.t_xgz_height_r_vol_up_model_mat : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] (Nm : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) (N m : ℕ) (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin m) K) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), IsFrame Nm L b g A → ∃ Mt : (𝓞 K →+* ℂ) → Matrix (Fin m) (Fin m) ℂ, (∀ σ, (Mt σ).det ≠ 0) ∧ (∀ σ, ∃ U ∈ Matrix.unitaryGroup (Fin m) ℂ, Mt ((starRingEnd ℂ).comp σ) = (Mt σ).map (starRingEnd ℂ) * U) ∧ ∀ (σ : K →+* ℂ) (x : Fin N → ℂ), ∑ a, ‖∑ k, Mt (σ.comp (algebraMap (𝓞 K) K)) k a * ∑ j, σ (g j k) * x j‖ ^ 2 = GlobalTheory.Adelic.archSize (A σ) x ^ 2 := by
  intro K V _ _ _ _ _ Nm L N m b g A hF
  obtain ⟨r, e, P, hP, hgP⟩ := PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_mat.exists_P g hF.full
  choose ext hext using PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_mat.exists_ext K
  have hu : ∀ σ : K →+* ℂ, ext (σ.comp (algebraMap (𝓞 K) K)) = σ := fun σ =>
    PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_mat.ext_unique K (hext _)
  have hc : ∀ τ, ext ((starRingEnd ℂ).comp τ) = (starRingEnd ℂ).comp (ext τ) := fun τ =>
    PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_mat.ext_unique K (by rw [hext, RingHom.comp_assoc, hext])
  refine ⟨fun τ => P.map (ext τ) * (Matrix.fromBlocks (A (ext τ)) 0 0 (1 : Matrix (Fin r) (Fin r) ℂ)).submatrix e e,
    fun τ => ?_, fun τ => ?_, fun σ x => ?_⟩
  · rw [Matrix.det_mul, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
    refine mul_ne_zero ?_ (hF.herm _)
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 hP
  · obtain ⟨U, hU, hB⟩ := PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_mat.exists_unitary (A (ext τ))
      (A ((starRingEnd ℂ).comp (ext τ))) (hF.herm _) (hF.herm _) (hF.conj _)
    refine ⟨(Matrix.fromBlocks U 0 0 (1 : Matrix (Fin r) (Fin r) ℂ)).submatrix e e, ?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff] at hU ⊢
      rw [Matrix.star_eq_conjTranspose] at hU ⊢
      rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_conjTranspose,
        Matrix.fromBlocks_multiply]
      simp [hU]
    · simp only []
      rw [hc, hB, Matrix.map_mul, Matrix.mul_assoc, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv,
        Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.map_map]
      simp
  · simp only [hu]
    have key : g.map σ * (P.map σ * (Matrix.fromBlocks (A σ) 0 0 (1 : Matrix (Fin r) (Fin r) ℂ)).submatrix e e) =
        (Matrix.fromCols (A σ) (0 : Matrix (Fin N) (Fin r) ℂ)).submatrix id e := by
      rw [← Matrix.mul_assoc, ← Matrix.map_mul, hgP, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv,
        Matrix.fromCols_map, Matrix.fromCols_mul_fromBlocks]
      simp
    have k2 : ∀ a, ∑ k, (P.map σ * (Matrix.fromBlocks (A σ) 0 0 (1 : Matrix (Fin r) (Fin r) ℂ)).submatrix e e) k a *
        ∑ j, σ (g j k) * x j = ∑ j, Matrix.fromCols (A σ) (0 : Matrix (Fin N) (Fin r) ℂ) j (e a) * x j := by
      intro a
      generalize P.map σ * (Matrix.fromBlocks (A σ) 0 0 (1 : Matrix (Fin r) (Fin r) ℂ)).submatrix e e = M at key
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      have := congrFun (congrFun key j) a
      rw [Matrix.submatrix_apply, id, Matrix.mul_apply] at this
      rw [← this, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.map_apply]; ring
    simp only [k2]
    rw [GlobalTheory.Adelic.archSize, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
      Equiv.sum_comp e (fun a => ‖∑ j, Matrix.fromCols (A σ) (0 : Matrix (Fin N) (Fin r) ℂ) j a * x j‖ ^ 2),
      Fintype.sum_sum_type]
    simp
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XXgzHeightRVolUpModelModel
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

namespace PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_model

theorem exists_comb {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω) {N m : ℕ} (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin m) K)
    (hg : Submodule.span K (Set.range g.col) = ⊤) (v : V) :
    ∃ c : Fin m → K, ev v = ∑ k, algebraMap K Ω (c k) * ev (∑ j, g j k • b j) := by
  have hmem : (⇑(b.repr v) : Fin N → K) ∈ Submodule.span K (Set.range g.col) := by
    rw [hg]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hmem
  refine ⟨c, ?_⟩
  have hv : v = ∑ k, c k • ∑ j, g j k • b j := by
    conv_lhs => rw [← b.sum_repr v]
    rw [← hc]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
    rfl
  rw [hv]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Algebra.smul_def]

theorem closure_eq_top {K V Ω : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω) {m : ℕ} (t : Fin m → Ω)
    (ht : ∀ v, ∃ c : Fin m → K, ev v = ∑ k, algebraMap K Ω (c k) * t k) (i : Fin m) (hi : t i ≠ 0)
    (hr : IntermediateField.adjoin K {a : Ω | ∃ v w, a = ev v / ev w} = ⊤) :
    Subfield.closure (Set.range (algebraMap (𝓞 K) Ω) ∪ {x | ∃ i j, x = t j / t i}) = ⊤ := by
  set F := Subfield.closure (Set.range (algebraMap (𝓞 K) Ω) ∪ {x | ∃ i j, x = t j / t i}) with hF
  have hK : ∀ x : K, algebraMap K Ω x ∈ F := by
    intro x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
    rw [map_div₀]
    have e : ∀ y : 𝓞 K, algebraMap K Ω (algebraMap (𝓞 K) K y) = algebraMap (𝓞 K) Ω y :=
      fun y => (IsScalarTower.algebraMap_apply (𝓞 K) K Ω y).symm
    rw [e, e]
    exact div_mem (Subfield.subset_closure (Or.inl ⟨a, rfl⟩)) (Subfield.subset_closure (Or.inl ⟨b, rfl⟩))
  have key : ∀ u, ev u / t i ∈ F := by
    intro u
    obtain ⟨c, hc⟩ := ht u
    rw [hc, Finset.sum_div]
    refine sum_mem fun k _ => ?_
    rw [mul_div_assoc]
    exact mul_mem (hK (c k)) (Subfield.subset_closure (Or.inr ⟨i, k, rfl⟩))
  have hS : {a : Ω | ∃ v w, a = ev v / ev w} ⊆ (F.toIntermediateField hK : Set Ω) := by
    rintro _ ⟨v, w, rfl⟩
    show ev v / ev w ∈ F
    rw [← div_div_div_cancel_right₀ hi (ev v) (ev w)]
    exact div_mem (key v) (key w)
  have hle := (IntermediateField.adjoin_le_iff).2 hS
  rw [hr] at hle
  exact eq_top_iff.2 fun x _ => hle (IntermediateField.mem_top : x ∈ (⊤ : IntermediateField K Ω))

end PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_model
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XXgzHeightRVolUpModelNef
section
namespace PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_nef

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ZH GlobalTheory.ZH.RatModel

variable {K V Ω : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
  {M : RatModel (𝓞 K) Ω}

theorem const_val {σ : K →+* ℂ} {y : Sp ℂ ⟶ M.Z} (hy : y ≫ M.s = spMap (σ.comp (algebraMap (𝓞 K) K))) (a : K) :
    algebraMap K Ω a ∈ M.O (y (IsLocalRing.closedPoint ℂ)) ∧ M.val y (algebraMap K Ω a) = σ a := by
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
  have hr := range_eq_singleton y (IsLocalRing.closedPoint ℂ)
  have hq0 : algebraMap (𝓞 K) K q ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
  have hσq : σ (algebraMap (𝓞 K) K q) ≠ 0 := (map_ne_zero σ).2 hq0
  have hv := fun c => val_algebraMap hy c
  have hu : IsUnit (⟨algebraMap (𝓞 K) Ω q, Subalgebra.algebraMap_mem _ q⟩ :
      M.O (y (IsLocalRing.closedPoint ℂ))) := (val_ne_zero_iff hr _).1 (by rw [hv]; exact hσq)
  obtain ⟨h0, hi⟩ := (isUnit_O_iff _).1 hu
  dsimp only at h0 hi
  have e : algebraMap K Ω (algebraMap (𝓞 K) K p / algebraMap (𝓞 K) K q) =
      algebraMap (𝓞 K) Ω p * (algebraMap (𝓞 K) Ω q)⁻¹ := by
    rw [map_div₀, div_eq_mul_inv, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hm : algebraMap (𝓞 K) Ω p * (algebraMap (𝓞 K) Ω q)⁻¹ ∈ M.O (y (IsLocalRing.closedPoint ℂ)) :=
    mul_mem (Subalgebra.algebraMap_mem _ p) hi
  rw [e]
  refine ⟨hm, ?_⟩
  have h1 := val_mul (specializes_of_range_eq hr) hm (Subalgebra.algebraMap_mem _ q)
  rw [inv_mul_cancel_right₀ h0, hv, hv] at h1
  rw [map_div₀, eq_div_iff hσq]
  exact h1.symm

theorem exists_coord {σ : K →+* ℂ} {y : Sp ℂ ⟶ M.Z} (hy : y ≫ M.s = spMap (σ.comp (algebraMap (𝓞 K) K)))
    (ev : V →ₗ[K] Ω) (c : Ω) {N : ℕ} (b : Module.Basis (Fin N) K V) {S : Set V} (hS : Submodule.span K S = ⊤)
    (hc : ∀ v ∈ S, ev v / c ∈ M.O (y (IsLocalRing.closedPoint ℂ))) :
    ∃ x : Fin N → ℂ, ∀ v, M.val y (ev v / c) = ∑ j, σ (b.repr v j) * x j := by
  have hr := specializes_of_range_eq (range_eq_singleton y (IsLocalRing.closedPoint ℂ))
  have hsm : ∀ (a : K) v, ev (a • v) / c = algebraMap K Ω a * (ev v / c) := fun a v => by
    rw [map_smul, Algebra.smul_def, mul_div_assoc]
  have hall : ∀ v, ev v / c ∈ M.O (y (IsLocalRing.closedPoint ℂ)) := fun v => by
    have hv : v ∈ Submodule.span K S := hS ▸ trivial
    induction hv using Submodule.span_induction with
    | mem _ h => exact hc _ h
    | zero => rw [map_zero, zero_div]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add (f := _), add_div]; exact add_mem ha hb
    | smul a v _ hv => rw [hsm]; exact mul_mem (const_val hy a).1 hv
  let ℓ : V →+ ℂ :=
    { toFun := fun v => M.val y (ev v / c)
      map_zero' := by rw [map_zero, zero_div]; exact val_zero y
      map_add' := fun a b => by rw [map_add (f := _), add_div]; exact val_add hr (hall a) (hall b) }
  refine ⟨fun j => ℓ (b j), fun v => ?_⟩
  change ℓ v = _
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [← b.sum_repr v, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  change M.val y _ = _
  rw [hsm, val_mul hr (const_val hy _).1 (hall _), (const_val hy _).2]
  rfl



end PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_nef

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
end

