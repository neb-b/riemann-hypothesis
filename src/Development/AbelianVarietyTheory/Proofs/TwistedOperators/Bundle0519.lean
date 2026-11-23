module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0474
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1468
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0163
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0501
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0506
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentUnitDecomposition
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section
namespace GlobalTheory.SplitCharValue

theorem values_of_rel (D : D7) (z : ℂ) (K : ℕ) (b : D.host.Eˣ) (m : D.what₂.Tau → ℤ) (hK : 0 < K)
    (h : z ^ K * ∏ τ, (tauE D τ (b : D.host.E) / (‖tauE D τ (b : D.host.E)‖ : ℂ)) ^ m τ = 1) :
    Mod1All z ∧ ∀ (q : ℕ) [Fact q.Prime], (∀ P : HeightOneSpectrum (𝓞 D.host.E), ((q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal →
      P.valuation D.host.E (b : D.host.E) = 1) → GlobalTheory.MovedKappaEx.UnitAt q z := by
  have : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨hz, H⟩ := GlobalTheory.HeckeVal.root_value (tauE D) m b z K hK h
  refine ⟨⟨hz, fun σ => H ℂ σ fun τ => ?_⟩, fun q hq hb lam => ?_⟩
  · have := IsCMField.complexEmbedding_complexConj D.host.E (σ.comp τ) (b : D.host.E)
    simp only [RingHom.comp_apply] at this
    rw [this, Complex.norm_conj]
  · obtain ⟨M, hM, i1⟩ := GlobalTheory.KerTie.MuqUnit.exists_coprime_mul_isIntegral hq.out (b : D.host.E)
      fun P hP => (hb P hP).le
    obtain ⟨M', hM', i2⟩ := GlobalTheory.KerTie.MuqUnit.exists_coprime_mul_isIntegral hq.out (b : D.host.E)⁻¹
      fun P hP => by rw [map_inv₀, hb P hP, inv_one]
    have key : ∀ ψ : D.host.E →+* ℂ_[q], ‖ψ (b : D.host.E)‖ = 1 := fun ψ => by
      have j1 := GlobalTheory.HeckeVal.norm_le_one_of_denom ψ hM i1
      have j2 := GlobalTheory.HeckeVal.norm_le_one_of_denom ψ hM' i2
      rw [map_inv₀, norm_inv] at j2
      have h0 : 0 < ‖ψ b‖ := norm_pos_iff.2 ((map_ne_zero _).2 b.ne_zero)
      exact le_antisymm j1 ((inv_le_one₀ h0).1 j2)
    rw [Formalism.MainNotions.TaylorLogMetric.lamC, dite_eq_left hz]
    refine H _ lam fun τ => ?_
    exact (key (lam.comp τ)).trans
      (key ((lam.comp τ).comp (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E))).symm

theorem inf_val (D : D7) (c : (Formalism.L2.Theta.AE D)ˣ →* Circle) (n : ℕ) (hc : Formalism.L2.Theta.IsHeckeChar D c)
    (hr : Formalism.L2.Theta.ResEta D c n) : ∃ m : D.what₂.Tau → ℤ, ∀ (k : D.host.Eˣ) (x : (Formalism.L2.Theta.AE D)ˣ),
      Formalism.L2.Theta.finPart D (x : Formalism.L2.Theta.AE D) = 1 →
      Formalism.L2.Theta.infPart D (x : Formalism.L2.Theta.AE D) = Formalism.L2.Theta.infPart D (Formalism.L2.Theta.incA D (k : D.host.E)) →
      ((c x : Circle) : ℂ) = ∏ τ, (tauE D τ (k : D.host.E) / (‖tauE D τ (k : D.host.E)‖ : ℂ)) ^ m τ := by
  classical
  obtain ⟨θ, hθ⟩ : ∃ θ : InfFam D, IsInfFam θ := GlobalTheory.DualPairCompare.exists_infFam D
  have H : ∀ τ, ∃ m : ℤ, ∀ x : (Formalism.L2.Theta.AE D)ˣ, Formalism.L2.Theta.finPart D (x : Formalism.L2.Theta.AE D) = 1 →
      (∀ τ', τ' ≠ τ → θ τ' (Formalism.L2.Theta.infPart D (x : Formalism.L2.Theta.AE D)) = 1) →
        ((c x : Circle) : ℂ) = (θ τ (Formalism.L2.Theta.infPart D (x : Formalism.L2.Theta.AE D)) / (‖θ τ (Formalism.L2.Theta.infPart D (x : Formalism.L2.Theta.AE D))‖ : ℂ)) ^ m := fun τ => by
    obtain ⟨a, m, -, -, h⟩ := GlobalTheory.SplitCharExp.exists_hasInfExp D θ c n τ hθ hc hr
    exact ⟨m, h θ hθ⟩
  choose m hm using H
  refine ⟨m, fun k x hx1 hx2 => ?_⟩
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨e, -, e1, e2⟩ := GlobalTheory.SplitCharExp.exists_real_hom h
  let z : D.what₂.Tau → ℂˣ := fun τ => Units.map (tauE D τ).toMonoidHom k
  let f : ∀ _ : D.what₂.Tau, ℂ →* Formalism.L2.Theta.AE D := fun τ => e.comp (MonoidHom.mulSingle (fun _ : D.what₂.Tau => ℂ) τ)
  have hθk : ∀ τ, θ τ (Formalism.L2.Theta.infPart D (Formalism.L2.Theta.incA D (k : D.host.E))) = tauE D τ k := fun τ => (hθ τ).1 k
  have ex : x = ∏ τ, Units.map (f τ) (z τ) := by
    apply Units.ext
    rw [Units.coe_prod]
    have e3 : (∏ τ, ((Units.map (f τ) (z τ) : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D)) = e (fun τ => tauE D τ k) := by
      change ∏ τ, e (Pi.mulSingle τ (tauE D τ k)) = _
      rw [← map_prod, Finset.univ_prod_mulSingle]
    rw [e3]
    exact GlobalTheory.SplitCharExp.ext_of_chart h (hx1.trans (e1 _).symm) fun τ => by rw [hx2, hθk, e2]
  rw [ex, map_prod]
  refine (map_prod Circle.coeHom _ _).trans (Finset.prod_congr rfl fun τ _ => ?_)
  have f2 : ∀ τ', θ τ' (Formalism.L2.Theta.infPart D ((Units.map (f τ) (z τ) : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D)) =
      (Pi.mulSingle τ (tauE D τ k) : D.what₂.Tau → ℂ) τ' := fun τ' => e2 _ τ'
  have := hm τ (Units.map (f τ) (z τ)) (e1 _) fun τ' ht => by rw [f2, Pi.mulSingle_eq_of_ne ht]
  rw [f2, Pi.mulSingle_eq_same] at this
  exact this

def finIso (D : D7) : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv.trans (GlobalTheory.Mem.Col2.afIso D.host.F D.host.E)

theorem finIso_one_tmul (D : D7) (x : D.host.E) : finIso D ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) =
    algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x := GlobalTheory.Mem.Col2.afIso_tmul_one _ _ x

theorem mem_intAE_iff (D : D7) (y : Af D.host.F ⊗[D.host.F] D.host.E) :
    y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (finIso D y P) ≤ 1 :=
  (GlobalTheory.HostAdeleIso.mem_intAE_iff_comm D y).trans (GlobalTheory.Mem.Col2.mem_rInt_iff _ _ _)


set_option maxHeartbeats 800000 in
theorem exists_pow_rel (D : D7) (x : (Formalism.L2.Theta.AE D)ˣ) (hx : Formalism.L2.Theta.infPart D (x : Formalism.L2.Theta.AE D) = 1) :
    ∃ (h : ℕ) (k : D.host.Eˣ) (y w : (Formalism.L2.Theta.AE D)ˣ), 0 < h ∧ Formalism.L2.Pj.FinUnit w ∧ Formalism.L2.Theta.finPart D (y : Formalism.L2.Theta.AE D) = 1 ∧
      Formalism.L2.Theta.infPart D (y : Formalism.L2.Theta.AE D) = Formalism.L2.Theta.infPart D (Formalism.L2.Theta.incA D (k : D.host.E)) ∧
      x ^ h * y = w * Units.map (Formalism.L2.Theta.incA D).toMonoidHom k ∧
      ∀ P : HeightOneSpectrum (𝓞 D.host.E), finIso D (Formalism.L2.Theta.finPart D (x : Formalism.L2.Theta.AE D)) P = 1 →
        P.valuation D.host.E (k : D.host.E) = 1 := by
  obtain ⟨Φ, -, -, h1, -, h3⟩ := GlobalTheory.DetRootRead.exists_adele_equiv_fin D (finIso D) (finIso_one_tmul D) (mem_intAE_iff D)
  obtain ⟨s, hs, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hs1 : ∀ z : Formalism.L2.Theta.AE D, (s z).1 = Formalism.L2.Theta.infPart D z := fun z => (hs z).1
  have hs2 : ∀ z : Formalism.L2.Theta.AE D, (s z).2 = Formalism.L2.Theta.finPart D z := fun z => (hs z).2
  have hfi := GlobalTheory.Mem.UnitIndex.finiteIndex_unitIdl_sup D.host.E
  obtain ⟨u, hu, _, ⟨k, rfl⟩, e⟩ := Subgroup.mem_sup.1 ((GlobalTheory.Mem.Chr.unitIdl D.host.E ⊔
    (Neutral.B1.diagUnits D.host.E).range).pow_index_mem (Units.map Φ.toRingHom.toMonoidHom x))
  generalize hh : (GlobalTheory.Mem.Chr.unitIdl D.host.E ⊔ (Neutral.B1.diagUnits D.host.E).range).index = h at e
  have h0 : 0 < h := hh ▸ Nat.pos_of_ne_zero hfi.index_ne_zero
  let Ψ : (AdeleRing (𝓞 D.host.E) D.host.E)ˣ →* (Formalism.L2.Theta.AE D)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom
  have hΨ : ∀ a, Φ ((Ψ a : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D) = a := fun a => Φ.apply_symm_apply _
  let K : (Formalism.L2.Theta.AE D)ˣ := Units.map (Formalism.L2.Theta.incA D).toMonoidHom k
  have e' : Ψ u * K = x ^ h := by
    have a1 : Ψ (Neutral.B1.diagUnits D.host.E k) = K := Units.ext (Φ.symm_apply_eq.2 (h1 k).symm)
    have a2 : Ψ (Units.map Φ.toRingHom.toMonoidHom x) = x := Units.ext (Φ.symm_apply_apply _)
    rw [← a1, ← map_mul, e, map_pow, a2]
  let g : Formalism.L2.Theta.AE D →* Formalism.L2.Theta.AE D := s.symm.toRingHom.toMonoidHom.comp
    ((MonoidHom.inl _ (Af D.host.F ⊗[D.host.F] D.host.E)).comp (Formalism.L2.Theta.infPart D).toMonoidHom)
  have g1 : ∀ a, Formalism.L2.Theta.infPart D (g a) = Formalism.L2.Theta.infPart D a := fun a =>
    (hs1 _).symm.trans (congrArg Prod.fst (s.apply_symm_apply (Formalism.L2.Theta.infPart D a, 1)))
  have g2 : ∀ a, Formalism.L2.Theta.finPart D (g a) = 1 := fun a =>
    (hs2 _).symm.trans (congrArg Prod.snd (s.apply_symm_apply (Formalism.L2.Theta.infPart D a, 1)))
  have hint : ∀ a ∈ GlobalTheory.Mem.Chr.unitIdl D.host.E, ∀ b : (Formalism.L2.Theta.AE D)ˣ,
      Formalism.L2.Theta.finPart D ((Ψ a * Units.map g b : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D) ∈ intAE D := fun a ha b => by
    have : Formalism.L2.Theta.finPart D ((Units.map g b : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D) = 1 := g2 _
    rw [Units.val_mul, RingHom.map_mul, this, mul_one, mem_intAE_iff, ← (h3 _).2, hΨ]
    exact fun P => (ha P).le
  refine ⟨h, k, Units.map g K, Ψ u * Units.map g K, h0, ⟨?_, hint u hu K, ?_⟩, g2 _, g1 _, ?_, fun P hP => ?_⟩
  · have a1 : Formalism.L2.Theta.infPart D ((Units.map g K : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D) = Formalism.L2.Theta.infPart D (K : Formalism.L2.Theta.AE D) := g1 _
    rw [Units.val_mul, RingHom.map_mul, a1, ← RingHom.map_mul, ← Units.val_mul, e', Units.val_pow_eq_pow_val,
      RingHom.map_pow, hx, one_pow]
  · rw [mul_inv, ← Ψ.map_inv u, ← (Units.map g).map_inv K]
    exact hint u⁻¹ ((GlobalTheory.Mem.Chr.unitIdl D.host.E).inv_mem hu) K⁻¹
  · rw [← e', mul_right_comm]
  · have a1 : (u : AdeleRing (𝓞 D.host.E) D.host.E).2 P * algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E) =
        ((Φ (x : Formalism.L2.Theta.AE D)).2 P) ^ h :=
      congrArg (fun a : (AdeleRing (𝓞 D.host.E) D.host.E)ˣ => (a : AdeleRing (𝓞 D.host.E) D.host.E).2 P) e
    rw [(h3 _).2, hP, one_pow] at a1
    have a2 := congrArg (Valued.v : Valuation (P.adicCompletion D.host.E) _) a1
    rw [map_mul, hu P, one_mul, map_one] at a2
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P (k : D.host.E)).symm.trans a2

theorem finIso_idem (D : D7) {e : Formalism.L2.Theta.AE D} (he : IsSplitIdem D e) {q : ℕ} (hq : GlobalTheory.MovedKappaEx.OffPrime e q)
    (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : ((q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) : finIso D (Formalism.L2.Theta.finPart D e) P = 0 := by
  obtain ⟨h1, h2, v, ε, hε, h4⟩ := he
  have hv := hq v ε hε h4
  obtain ⟨α, rfl, -, hα⟩ := hε
  have hne : P.under (𝓞 D.host.F) ≠ v := by
    rintro rfl
    apply hv
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (q : 𝓞 D.host.F) ∈ P.asIdeal
    rwa [map_natCast]
  have h5 : finIso D (Formalism.L2.Theta.finPart D (e + cA D e)) P = 0 := by
    rw [h4]
    refine (GlobalTheory.SplitProj.afIso_one_tmul_apply α P).trans ?_
    have : α (P.under (𝓞 D.host.F)) = 0 := hα _ hne
    rw [GlobalTheory.AdeleBaseChange.adMap_apply, this, map_zero]
  have h6 : e = e * (e + cA D e) := by rw [mul_add, h1, h2, add_zero]
  rw [h6, RingHom.map_mul, RingEquiv.map_mul]
  show finIso D (Formalism.L2.Theta.finPart D e) P * finIso D (Formalism.L2.Theta.finPart D (e + cA D e)) P = 0
  rw [h5, mul_zero]

theorem char_split_value (D : D7) (c : (Formalism.L2.Theta.AE D)ˣ →* Circle) (n : ℕ) (hc : Formalism.L2.Theta.IsHeckeChar D c)
    (hr : Formalism.L2.Theta.ResEta D c n) (e : Formalism.L2.Theta.AE D) (he : IsSplitIdem D e) (x₀ : (Formalism.L2.Theta.AE D)ˣ)
    (a : Formalism.L2.Theta.AE D) (hx : (x₀ : Formalism.L2.Theta.AE D) = e * a + (1 - e)) :
    Mod1All ((c x₀ : Circle) : ℂ) ∧ ∀ (q : ℕ) [Fact q.Prime], GlobalTheory.MovedKappaEx.OffPrime e q →
      GlobalTheory.MovedKappaEx.UnitAt q ((c x₀ : Circle) : ℂ) := by
  obtain ⟨m, hm⟩ := inf_val D c n hc hr
  obtain ⟨-, -, -, M, hM, hMu⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D c hc.1
  have hinf : Formalism.L2.Theta.infPart D (x₀ : Formalism.L2.Theta.AE D) = 1 := by
    rw [hx, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_mul, RingHom.map_one,
      GlobalTheory.SplitScalar.infPart_splitIdem he, zero_mul, sub_zero, zero_add]
  obtain ⟨h, k, y, w, hh, hw, hy1, hy2, e1, hk⟩ := exists_pow_rel D x₀ hinf
  have e2 : c x₀ ^ (h * M) * c y ^ M = 1 := by
    rw [pow_mul, ← mul_pow, ← map_pow, ← map_mul, e1, map_mul, hc.2 k, mul_one, hMu w hw]
  have e3 : ((c x₀ : Circle) : ℂ) ^ (h * M) *
      ∏ τ, (tauE D τ (k : D.host.E) / (‖tauE D τ (k : D.host.E)‖ : ℂ)) ^ (m τ * M) = 1 := by
    simp only [zpow_mul, zpow_natCast]
    rw [Finset.prod_pow, ← hm k y hy1 hy2, ← Circle.coe_pow, ← Circle.coe_pow, ← Circle.coe_mul, e2, Circle.coe_one]
  obtain ⟨h1, h2⟩ := values_of_rel D _ (h * M) k (fun τ => m τ * M) (Nat.mul_pos hh hM) e3
  refine ⟨h1, fun q _ hq => h2 q fun P hP => hk P ?_⟩
  rw [hx, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_mul, RingHom.map_one, RingEquiv.map_add (e := _), RingEquiv.map_sub,
    RingEquiv.map_mul, RingEquiv.map_one]
  show finIso D (Formalism.L2.Theta.finPart D e) P * finIso D (Formalism.L2.Theta.finPart D a) P + (1 - finIso D (Formalism.L2.Theta.finPart D e) P) = 1
  rw [finIso_idem D he hq P hP, zero_mul, sub_zero, zero_add]

theorem offPrime_conj {D : D7} {e : Formalism.L2.Theta.AE D} {q : ℕ} (h : GlobalTheory.MovedKappaEx.OffPrime e q) :
    GlobalTheory.MovedKappaEx.OffPrime (cA D e) q := fun v ε hv hε =>
  h v ε hv (by rw [← hε, GlobalTheory.MovedIdem.cA_cA, add_comm])

theorem defPair_inRange {T : Type} {m : ℕ} {p : Pair T} (h : DefPair m p) : p.InRange m := by
  cases p <;> simp only [DefPair, Pair.InRange, Pair.big, Node.InRange] at h ⊢ <;> omega

end GlobalTheory.SplitCharValue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameFunctionalVacuumIrreducibility
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.Irr

variable {D : D7}

theorem thPair_self_ne_zero {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    (v : VolM D T.rank S.rank) {f₀ : WO S T → ℂ} (hf : IsThetaFunO ψ S T f₀) (hne : f₀ ≠ 0) :
    thPair v.μ v.𝓕 f₀ f₀ ≠ 0 := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  haveI : BorelSpace (Mx D T.rank S.rank) := ⟨rfl⟩
  haveI : DiscreteTopology (ratMx D T.rank S.rank) := i5
  haveI : Countable (ratMx D T.rank S.rank) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨hμ, hF, h1⟩ := v.covol
  haveI := hμ
  haveI : IsFiniteMeasure (v.μ.restrict v.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  obtain ⟨C, hC⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hf
  have e : ∀ w, f₀ w * star (f₀ w) = ((‖f₀ w‖ ^ 2 : ℝ) : ℂ) := fun w => by
    rw [Complex.star_def, Complex.mul_conj']; push_cast; rfl
  have hint : Integrable (fun w => ‖f₀ w‖ ^ 2) (v.μ.restrict v.𝓕) :=
    Integrable.of_bound (hf.cont.norm.pow 2).measurable.aestronglyMeasurable (C ^ 2)
      (Filter.Eventually.of_forall fun w => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hC w) 2)
  intro h0
  have h2 : (∫ w in v.𝓕, ‖f₀ w‖ ^ 2 ∂v.μ) = 0 := by
    have : thPair v.μ v.𝓕 f₀ f₀ = ((∫ w in v.𝓕, ‖f₀ w‖ ^ 2 ∂v.μ : ℝ) : ℂ) := by
      unfold thPair
      simp_rw [e]
      exact integral_ofReal
    rw [this] at h0
    exact_mod_cast h0
  have h3 : ∫⁻ w in v.𝓕, ‖f₀ w‖ₑ ^ 2 ∂v.μ = 0 := by
    have en : ∀ z : ℂ, ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := fun z => by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    simp_rw [en]
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun w => by positivity), h2,
      ENNReal.ofReal_zero]
  exact hne (GlobalTheory.OrientedHeis.eq_zero_of_lintegral_eq_zero (ratMx D T.rank S.rank) v.μ v.𝓕 hF f₀ hf.cont
    (fun γ hγ w => GlobalTheory.OrientedHeis.theta_norm_periodic hψ hf γ hγ w) h3)

theorem irr : ∀ D : D7, Irr D := by
  intro D ψ hψ S T Γ ℓ hℓ f₀ hf₀ hne hann f hf
  obtain ⟨v⟩ := (GlobalTheory.Unf.VolExist.measures_exist D).2.2.1 T.rank S.rank
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  haveI : BorelSpace (Mx D T.rank S.rank) := ⟨rfl⟩
  haveI := v.covol.1
  haveI : SFinite v.μ := inferInstance
  obtain ⟨hint, hmoy⟩ := _root_.GlobalTheory.MoyalTheta.orthogonality D ψ hψ S T v f f₀ hf.1 hf₀.1
  have heq : (fun x => ∫ w, thPair v.μ v.𝓕 f (heisO ψ S T w f₀) * heisO ψ S T w f₀ x ∂v.μ) =
      thPair v.μ v.𝓕 f₀ f₀ • f := funext fun x => by rw [hmoy x]; rfl
  have hth : IsThetaFunO ψ S T (fun x => ∫ w, thPair v.μ v.𝓕 f (heisO ψ S T w f₀) * heisO ψ S T w f₀ x ∂v.μ) := by
    rw [heq]; exact GlobalTheory.OrientedHeis.theta_smul _ hf.1
  have hsup := hℓ.sup f₀ hf₀.1 v.μ _ hint hth
  rw [heq, hℓ.smul _ _ hf.1] at hsup
  have hz : ∀ w, thPair v.μ v.𝓕 f (heisO ψ S T w f₀) * ℓ (heisO ψ S T w f₀) = 0 := fun w => by
    by_cases hw : w ∈ Ann ψ S T Γ
    · rw [hann w hw, mul_zero]
    · rw [(_root_.GlobalTheory.Asc.annVac D ψ hψ S T Γ).2.2 v f f₀ hf hf₀ w hw, zero_mul]
  simp_rw [hz, integral_zero] at hsup
  exact (mul_eq_zero.1 hsup).resolve_left (thPair_self_ne_zero hψ v hf₀.1 hne)

end GlobalTheory.Irr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TorusMixedCoordinateSumLeSobolevSeminormStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_mixedCoordinate_sum_le_sobolev_seminorm : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (θ : InfFam D), IsInfFam θ →
    ∀ (V X S₀ : HSp D) (r : ℕ) (d : GlobalTheory.MixModel.HypDec V S₀ r) (μ' : Measure (Mx D X.rank r))
    (𝓕' : Set (Mx D X.rank r)), IsCovolOne (GlobalTheory.MixModel.ratMx D X.rank r) μ' 𝓕' → ∀ (c : ℝ), 0 < c →
    ∀ (K₀ : Set (WO V X)), K₀ ∈ nhds (0 : WO V X) → IsCompact K₀ →
    ∀ (μ : Measure (WO V X)) (𝓕 : Set (WO V X)), IsCovolOne (ratL X V) μ 𝓕 →
    ∃ (k A : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ Ψ : WO V X → ℂ, IsThetaFunO ψ V X Ψ →
      (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ V X (n • u) Ψ = Ψ) →
      ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ α : Mx D r r, α.map (finPart D) = 1 →
        (∀ τ, compAt θ τ α = diagonal (fun i => (t i : ℂ))) →
        ∑' ξ : Matrix (Fin X.rank) (Fin r) D.host.E, ‖d.mixS X ψ μ' 𝓕' Ψ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) 0‖ₑ ≤
          ENNReal.ofReal (C * (n : ℝ) ^ A * (GlobalTheory.Size.sobO (V := V) (W := X) ψ θ μ 𝓕 k Ψ).toReal) := by
  first | exact @GlobalTheory.TorusMixedSum.sum_mixS_le | exact GlobalTheory.TorusMixedSum.sum_mixS_le | (intros; apply GlobalTheory.TorusMixedSum.sum_mixS_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryArchimedeanLineOperatorsOneParameter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

namespace GlobalTheory.LineGroup

theorem archOp_oneParam : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W,
    ∀ T : ℝ → SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')),
    (∀ (t : ℝ) (f : SInf F (Fin a × Fin (a + a'))), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (T t f)) →
    (∀ (s t : ℝ) (f : SInf F (Fin a × Fin (a + a'))), T (s + t) f = T s (T t f)) ∧ ∀ f : SInf F (Fin a × Fin (a + a')), T 0 f = f := by
  intro F E _ _ _ _ _ σ a a' B G X om om' _ γ _ T hA
  obtain ⟨r₀, hR, hinj⟩ := GlobalTheory.ArchUniq.exists_admissible_finite_factor (F := F) (Fin a × Fin (a + a'))
  refine ⟨fun s t f => hinj _ _ ?_, fun f => hinj _ _ ?_⟩
  · rw [← hA (s + t) f r₀ (hR f), ← hA s (T t f) r₀ (hR _), ← hA t f r₀ (hR f), ofAdd_add, map_mul,
      show ((1 : UA σ G.V.J), γ (Multiplicative.ofAdd s) * γ (Multiplicative.ofAdd t)) =
        ((1 : UA σ G.V.J), γ (Multiplicative.ofAdd s)) * (1, γ (Multiplicative.ofAdd t)) by
          simp [Prod.mk_mul_mk], map_mul, Module.End.mul_apply]
  · rw [← hA 0 f r₀ (hR f), ofAdd_zero, map_one, Prod.mk_one_one, map_one, Module.End.one_apply]

end GlobalTheory.LineGroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryArchimedeanLinePairOperatorsOneParameter
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

namespace GlobalTheory.LineGroupPair

theorem archOp_oneParam_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ γ ∈ Lines σ W, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (T t f)) →
        (∀ (s t : ℝ) (f : SInf F (Fin n × Fin d)), T (s + t) f = T s (T t f)) ∧ ∀ f : SInf F (Fin n × Fin d), T 0 f = f := by
  intro F E _ _ _ _ _ σ _ n d X W M ψ χX χW om _ _ _ _ _ _ _ _ _ _ γ _ T hA
  obtain ⟨r₀, hR, hinj⟩ := GlobalTheory.ArchUniq.exists_admissible_finite_factor (F := F) (Fin n × Fin d)
  refine ⟨fun s t f => hinj _ _ ?_, fun f => hinj _ _ ?_⟩
  · rw [← hA (s + t) f r₀ (hR f), ← hA s (T t f) r₀ (hR _), ← hA t f r₀ (hR f), ofAdd_add, map_mul,
      show ((1 : UA σ X.J), γ (Multiplicative.ofAdd s) * γ (Multiplicative.ofAdd t)) =
        ((1 : UA σ X.J), γ (Multiplicative.ofAdd s)) * (1, γ (Multiplicative.ofAdd t)) by
          simp [Prod.mk_mul_mk], map_mul, Module.End.mul_apply]
  · rw [← hA 0 f r₀ (hR f), ofAdd_zero, map_one, Prod.mk_one_one, map_one, Module.End.one_apply]

end GlobalTheory.LineGroupPair
end

