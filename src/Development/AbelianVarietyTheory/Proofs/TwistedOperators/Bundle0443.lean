module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0424
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0252
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqVolMulSum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0252

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharTrivialOnIdempotentIntegralUnits
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChrOff

theorem idem_apply_eq_one {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
    (a : FiniteAdeleRing (𝓞 E) E) (ha : a * a = a)
    (h : ∀ x ∈ P.asIdeal, x ≠ 0 →
      ¬ ∀ Q, Valued.v ((a * algebraMap E (FiniteAdeleRing (𝓞 E) E) ((x : E)⁻¹)) Q) ≤ 1) : a P = 1 := by
  have h01 : ∀ Q, a Q ≠ 0 → a Q = 1 := fun Q hQ =>
    mul_left_cancel₀ hQ (by rw [← GlobalTheory.PlaceIdem.mul_ap, ha, mul_one])
  refine h01 P fun h0 => ?_
  obtain ⟨n, hn, x, hx⟩ := GlobalTheory.IdemRes.exists_pow_eq_span P.asIdeal P.ne_bot
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.2 rfl] at hx
    exact P.ne_bot (pow_eq_zero_iff hn.ne' |>.1 hx)
  refine h x (Ideal.pow_le_self hn.ne' (hx ▸ Ideal.mem_span_singleton_self x)) hx0 fun Q => ?_
  rw [GlobalTheory.PlaceIdem.mul_ap]
  by_cases hQ : a Q = 0
  · rw [hQ, zero_mul, map_zero]; exact zero_le
  · rw [h01 Q hQ, one_mul, GlobalTheory.PlaceIdem.val_inv_le_one Q hx0]
    intro hxQ
    have := Q.isPrime
    have h1 : P.asIdeal ^ n ≤ Q.asIdeal := by rw [hx]; exact (Ideal.span_singleton_le_iff_mem _).2 hxQ
    have h2 : P.asIdeal ≤ Q.asIdeal := Ideal.IsPrime.le_of_pow_le h1
    have h3 : P = Q := HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top h2)
    exact hQ (h3 ▸ h0)

variable {D : D7}

theorem exists_conj_mem {P P' : Pl D.host.E} (h : Formalism.IndefR.Lev.IsConjPl P P') {x : 𝓞 D.host.E}
    (hx : x ∈ P'.asIdeal) : ∃ y ∈ P.asIdeal, D.sp.cm.sig (y : D.host.E) = (x : D.host.E) := by
  let s : 𝓞 D.host.E →+* 𝓞 D.host.E := RingOfIntegers.mapRingHom (D.sp.cm.sig : D.host.E →+* D.host.E)
  have hs : ∀ y, (s y : D.host.E) = star (y : D.host.E) := fun _ => rfl
  have hle : P.asIdeal ≤ P'.asIdeal.comap s := fun c hc => by
    obtain ⟨c', hc', e⟩ := h c hc
    have : s c = c' := RingOfIntegers.ext (by rw [hs, e])
    rw [Ideal.mem_comap, this]; exact hc'
  have he := P.isMaximal.eq_of_le (Ideal.comap_ne_top s P'.isPrime.ne_top) hle
  have hss : s (s x) = x := RingOfIntegers.ext (by rw [hs, hs, star_star])
  refine ⟨s x, ?_, congrArg Subtype.val hss⟩
  rw [he, Ideal.mem_comap, hss]; exact hx

section
variable (ι : (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
  (h1 : ∀ x : D.host.E, ι ((1 : GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] x) =
    algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x)
  (h2 : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1)
include h1 h2

theorem comp_eq_one {f : AE D} (hf : f * f = f) (P : Pl D.host.E)
    (h : ∀ x ∈ P.asIdeal, x ≠ 0 → finPart D (f * incA D ((x : D.host.E)⁻¹)) ∉ intAE D) :
    ι (finPart D f) P = 1 := by
  refine idem_apply_eq_one P _ (by rw [← map_mul, ← RingHom.map_mul, hf]) fun x hx hx0 hc => h x hx hx0 ?_
  have e : finPart D (incA D ((x : D.host.E)⁻¹)) = (1 : GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] ((x : D.host.E)⁻¹) := rfl
  rw [h2, RingHom.map_mul, map_mul, e, h1]
  exact hc

theorem comp_idem {f : AE D} {P : Pl D.host.E} (hf : Formalism.L2.NTheta.IsIdemAt f P) : ι (finPart D f) P = 1 :=
  comp_eq_one ι h1 h2 hf.1.1 P fun x hx hx0 => (hf.2 x hx0).1 hx

theorem comp_conj_idem {f : AE D} {P P' : Pl D.host.E} (hf : Formalism.L2.NTheta.IsIdemAt f P)
    (hc : Formalism.IndefR.Lev.IsConjPl P P') : ι (finPart D (cA D f)) P' = 1 := by
  refine comp_eq_one ι h1 h2 (by rw [← RingHom.map_mul, hf.1.1]) P' fun x hx hx0 hi => ?_
  obtain ⟨y, hy, hyx⟩ := exists_conj_mem hc hx
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hx0 (RingOfIntegers.ext (hyx.symm.trans (map_zero _)))
  refine (hf.2 y hy0).1 hy ?_
  have e : cA D (incA D ((y : D.host.E)⁻¹)) = incA D ((x : D.host.E)⁻¹) := by
    rw [← hyx, ← map_inv₀ D.sp.cm.sig]; rfl
  rw [← e, ← RingHom.map_mul, GlobalTheory.PlaceIdem.finPart_cA] at hi
  have := GlobalTheory.PlaceIdem.sig_mem D hi
  rwa [GlobalTheory.PlaceIdem.sig_sig] at this

end

theorem exists_idem_mul {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) {PP : Pl D.host.E} (hPP : PP ∈ P) :
    ∃ f : AE D, Formalism.L2.NTheta.IsIdemAt f PP ∧ f * (e + cA D e) = f ∧ cA D f * (e + cA D e) = cA D f := by
  obtain ⟨⟨es, h1, h2⟩, h3⟩ := he
  have h4 : es PP * e = es PP := by
    rw [h2]
    refine GlobalTheory.PlaceModelSum.mul_sum_orth (fun i hi => (h1 i hi).1) (fun i hi j hj hij => ?_) hPP
    refine (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (h1 i hi).1 (h1 j hj).1).resolve_left fun h => hij ?_
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    by_cases hx : x = 0
    · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
    · rw [(h1 i hi).2 x hx, (h1 j hj).2 x hx, h]
  have h5 : es PP * (e + cA D e) = es PP := by
    rw [mul_add, h4, ← h4, mul_assoc, h3, mul_zero, add_zero]
  refine ⟨es PP, h1 PP hPP, h5, ?_⟩
  have h6 := congrArg (cA D) h5
  rwa [RingHom.map_mul, RingHom.map_add, cA_cA, add_comm] at h6

theorem unrOff_of_unrAt : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (P : Finset (Pl D.host.E)) (e : AE D), ChrEq c χ → IsIdemSum e P → (∀ PP', PP' ∉ P → (∀ PP ∈ P, ¬ Formalism.IndefR.Lev.IsConjPl PP PP') → χ.UnrAt PP') → UnrOff (e + cA D e) c := by
  intro D c χ P₀ e hc he hu x hx1 hx2 hx3 hb
  classical
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2
    (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc
  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom x)
  have hv : ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι (finPart D (x : AE D)) P) = 1 := by
    intro P
    have a := (h2 _).1 hx2 P
    have b := (h2 _).1 hx3 P
    have e : ι (finPart D (x : AE D)) * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    have e' : Valued.v (ι (finPart D (x : AE D)) P) * Valued.v (ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P) = 1 := by
      rw [← map_mul]
      have : ι (finPart D (x : AE D)) P * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P = 1 :=
        congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z P) e
      rw [this, map_one]
    refine le_antisymm a ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := e'.symm
      _ ≤ Valued.v (ι (finPart D (x : AE D)) P) * 1 := mul_le_mul_right b _
      _ = _ := mul_one _
  have hone : ∀ (f : AE D) (P : HeightOneSpectrum (𝓞 D.host.E)), f * (e + cA D e) = f → ι (finPart D f) P = 1 →
      ι (finPart D (x : AE D)) P = 1 := by
    intro f P hf hP
    have e1 : f * (x : AE D) = f := by rw [← hf, mul_assoc, hb]
    have e2 : ι (finPart D f) * ι (finPart D (x : AE D)) = ι (finPart D f) := by
      rw [← map_mul, ← RingHom.map_mul, e1]
    have e3 : ι (finPart D f) P * ι (finPart D (x : AE D)) P = ι (finPart D f) P :=
      congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z P) e2
    rwa [hP, one_mul] at e3
  have hunr : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ι (finPart D (x : AE D)) P ≠ 1 → χ.UnrAt P := by
    intro P hP
    refine hu P (fun hm => hP ?_) fun PP hm hcj => hP ?_
    · obtain ⟨f, f1, f2, -⟩ := exists_idem_mul he hm
      exact hone f P f2 (comp_idem ι h1 h2 f1)
    · obtain ⟨f, f1, -, f3⟩ := exists_idem_mul he hm
      exact hone _ P f3 (comp_conj_idem ι h1 h2 f1 hcj)
  have key := hprod x hx1 S (fun P => if ι (finPart D (x : AE D)) P = 1 then 1 else k P) (fun P hP => by
    by_cases h : ι (finPart D (x : AE D)) P = 1
    · rw [if_pos h, h, Units.val_one, map_one, map_one, map_one, sub_self, map_zero]
      exact ⟨rfl, zero_le⟩
    · rw [if_neg h]
      exact ⟨(hS P hP).1, (hS P hP).2.1⟩) hS'
  apply Subtype.ext
  refine key.trans (Finset.prod_eq_one fun P hP => ?_)
  by_cases h : ι (finPart D (x : AE D)) P = 1
  · rw [if_pos h, map_one, Units.val_one]
  · rw [if_neg h]
    have a' : Valued.v (ι (finPart D (x : AE D)) P) = P.valuation D.host.E (k P : D.host.E) := (hS P hP).1
    rw [hv P] at a'
    have hun : Formalism.L2.Host.IsUnitAt P (Formalism.L2.Host.atFin P (k P)) := by
      show Valued.v (((k P : D.host.E)) : P.adicCompletion D.host.E) = _
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← a']
    show ((χ.loc P (Formalism.L2.Host.atFin P (k P)) : ℂˣ) : ℂ) = 1
    rw [hunr P h _ hun, Units.val_one]

end GlobalTheory.ChrOff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InjKOfSeparatesLinB
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory.RowEx

theorem injK_of_separates_linB (hS : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate) (hL : LinB) : InjK := by
  refine GlobalTheory.RowTest.injK_of_separates hS ?_
  rcases hL with ⟨C0, hL⟩
  refine ⟨C0, fun ε CF hCF => ?_⟩
  obtain ⟨x0, hL⟩ := hL ε CF hCF
  refine ⟨x0, fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F hset ch hch hsc ρ ξ a u => ?_⟩
  exact hL D large₂ hε hx Γ Pl0 T A Ks R F hset (ch.withReal ρ ξ) hsc (hch.toIsBase.withReal ρ ξ) a u


end GlobalTheory.RowEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnThetaKOMulCusp
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DownConv

open GlobalTheory.Grid

variable {D : D7}

theorem MeasDat.haar_fd {N : Node D} {m : N.MeasDat} {df : Prop} {K : Subgroup (GL (Fin N.V.rank) (Lev.EAf D))}
    (h : m.Is df K) : m.ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ N.V) m.fd m.ν := by
  by_cases hd : df
  · exact ⟨(h.1 hd).1.1, (h.1 hd).2⟩
  · exact ⟨(h.2 hd).1.1, (h.2 hd).2⟩

theorem integrableOn_thetaKO_mul_cusp (hP : GlobalTheory.Published.CuspRapidDecay) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    (hθ : IsInfFam θ) (ε : Bool) {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {ω : WRep S T}
    (hω : IsWeilDatumO ψ (sgn ε S) T χS χT (ω.toSgn ε)) {Φ : WO S T → ℂ} (hΦ : IsThetaFunO ψ (sgn ε S) T Φ)
    {ν : Measure (GA D S)} {𝓕 : Set (GA D S)} (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ S) 𝓕 ν)
    {φ : GA D S → ℂ} (hφ : IsAutFunSm θ S φ) (hc : IsCuspFun S φ) (h : GA D T) :
    IntegrableOn (fun g => thetaKO ω g h Φ * φ g) 𝓕 ν := by
  have : BorelSpace (GA D S) := ⟨rfl⟩
  have hR : GlobalTheory.Grow.RapidDec S φ := GlobalTheory.Grow.rapidDec_of_cuspForm hP hθ hφ hc
  have e : ∀ g, thetaKO ω g h Φ = thetaKO (ω.toSgn ε) ((ofSgn ε S).symm g) h Φ := fun g => by
    show ω (g, h) Φ 0 = ω (ofSgn ε S ((ofSgn ε S).symm g), h) Φ 0
    rw [MulEquiv.apply_symm_apply]
  have hcont : Continuous fun g => thetaKO ω g h Φ := by
    simp only [e]
    exact (hω.om_cont Φ hΦ 0).comp ((continuous_ofSgn_symm ε S).prodMk continuous_const)
  have hinv : ∀ γ ∈ GQ S, ∀ g, thetaKO ω (γ * g) h Φ = thetaKO ω g h Φ := fun γ hγ g => by
    rw [e, e, map_mul]
    refine GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_left_fst hω hΦ h _ ?_ _
    rw [GlobalTheory.SgnIdent.mem_GQ_sgn, MulEquiv.apply_symm_apply]
    exact hγ
  have hg : GlobalTheory.Grow.ModGrowth S fun g => thetaKO ω g h Φ := by
    obtain ⟨C, A, hC⟩ := GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_modGrowth_fst hθ hω hΦ h
    exact ⟨C, A, fun g => by simp only [e]; exact hC _⟩
  exact hR.integrableOn_modGrowth_mul hν h𝓕 hg hinv hcont.measurable.aestronglyMeasurable

end GlobalTheory.DownConv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqFinClSumAvg
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.DefiniteClassReal

theorem isReps_transfer {Γ A B : Type} [Group Γ] [Group A] [Group B] (ι : Γ →* A) (ι' : Γ →* B) (e : A ≃* B)
    (he : ∀ γ, e (ι γ) = ι' γ) (J : Subgroup A) (J' : Subgroup B) (hJ : ∀ a, e a ∈ J' ↔ a ∈ J) {I : Type} (y : I → A)
    (h : Bridge.IsReps ι J y) : Bridge.IsReps ι' J' (fun i => e (y i)) := by
  intro b
  obtain ⟨i, ⟨γ, k, hk⟩, hu⟩ := h (e.symm b)
  refine ⟨i, ⟨γ, ⟨e k, (hJ k).2 k.2⟩, ?_⟩, ?_⟩
  · have := congrArg e hk
    rw [e.apply_symm_apply] at this
    rw [this, map_mul, map_mul, he]
  · rintro j ⟨γ', k', hk'⟩
    refine hu j ⟨γ', ⟨e.symm k', (hJ _).1 (by rw [e.apply_symm_apply]; exact k'.2)⟩, ?_⟩
    apply e.injective
    rw [e.apply_symm_apply, hk', map_mul, map_mul, he, e.apply_symm_apply]

theorem stab_transfer {Γ A B : Type} [Group Γ] [Group A] [Group B] (ι : Γ →* A) (ι' : Γ →* B) (e : A ≃* B)
    (he : ∀ γ, e (ι γ) = ι' γ) (J : Subgroup A) (J' : Subgroup B) (hJ : ∀ a, e a ∈ J' ↔ a ∈ J) (x : A) :
    Bridge.stab ι' J' (e x) = Bridge.stab ι J x := by
  ext γ
  rw [Bridge.mem_stab, Bridge.mem_stab, ← he, ← map_inv, ← map_mul, ← map_mul, hJ]

end GlobalTheory.DefiniteClassReal

namespace GlobalTheory.DefiniteClassReal
open GlobalTheory.FunObj GlobalTheory.ClassRegroup GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral GlobalTheory.DefiniteClassAvg

theorem integral_eq_finClSum_avg : ∀ {D : D7} (V : HSp D), (∀ φ : D.host.E →+* ℂ, (V.gram.map φ).PosDef) →
    ∀ (K K'' : Subgroup (GL (Fin V.rank) (Lev.EAf D))), IsOpenCompactLevel V K → IsOpenCompactLevel V K'' → K'' ≤ K →
    ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), IsMeasDef V K μ 𝓕 → ∀ (Φ : GA D V → ℂ),
    (∀ γ ∈ GQ V, ∀ g, Φ (γ * g) = Φ g) → (∀ k ∈ Lev.levA V K'', ∀ g, Φ (g * k) = Φ g) →
    (∀ z, Continuous fun k : GinfC V => Φ (z * k)) →
    Finite (FinCl V K'') ∧ ∃ κ : Measure (GinfC V), κ.IsHaarMeasure ∧ IsProbabilityMeasure κ ∧
      ∫ g in 𝓕, Φ g ∂μ = ∑ᶠ c : FinCl V K'',
        ((μ ((K''.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V))).toReal : ℂ) / (gamOrd V K'' c.out : ℂ) *
          ∫ k, Φ ((c.out : GA D V) * k) ∂κ := by
  intro D V hV K K'' hK hK'' hle μ 𝓕 hμ Φ hl hr hc

  let V' : HSp D := { V with sig := fun _ => (V.rank, 0) }
  have hS' : V'.SigOK := fun τ => GlobalTheory.Proof.GenusMassSignature.hasSignature_of_posDef (hV τ)
  have hD' : V'.IsDefinite := fun τ => Or.inl rfl
  have hGc : IsCompact (GinfC V : Set (GA D V)) := Formalism.IndefR.Eqv.isCompact_GinfC (V := V') hS' hD'
  haveI : CompactSpace (GinfC V) := isCompact_iff_compactSpace.1 hGc
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hLC := hT.1
  have hSC := hT.2.1
  have hB := hT.2.2.2.1
  have hG := hT.2.2.2.2.1
  have hC := hT.2.2.2.2.2.2
  have hHaar := hμ.1.1
  have hfin0 : Finite (FinCl V K'') := (finite_finCl_and_gamOrd V K'' hV hK'').1
  letI : Fintype (FinCl V K'') := Fintype.ofFinite _

  let κ : Measure (GinfC V) := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (GinfC V))
  haveI hκH : κ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  have hκ1 : κ Set.univ = 1 := by
    have := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (GinfC V)))
    simpa using this
  haveI : IsProbabilityMeasure κ := ⟨hκ1⟩
  refine ⟨hfin0, κ, hκH, inferInstance, ?_⟩

  let e := finEquiv V
  have he : ∀ γ, e (((finPt V).comp (GQ V).subtype) γ) = Bridge.ratF V γ := fun γ => e.apply_symm_apply _
  have hJe : ∀ a, e a ∈ levelFin V K'' ↔ a ∈ K''.comap (finG V) := fun a => Iff.rfl
  have hy := isReps_transfer _ _ e he _ _ hJe _ (isReps_out V K'')
  let y : FinCl V K'' → Bridge.Gf V := fun c => e (Quotient.out c)
  let z : FinCl V K'' → GA D V := fun c => ((Quotient.out c : GfC V) : GA D V)
  have hz : ∀ c, (finHom V).rangeRestrict (z c) = y c := fun c => rfl

  let J : Subgroup (GA D V) := K''.comap (Lev.finE V)
  let JK : Subgroup (GA D V) := K.comap (Lev.finE V)
  have hJo : IsOpen (J : Set (GA D V)) := hK''.1
  have hJJK : J ≤ JK := fun x hx => hle hx
  have hJK1 : μ JK = 1 := GlobalTheory.Mass.Levels.measure_comap_finE hμ.1
  have hJtop : μ J ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [hJK1]; exact ENNReal.one_ne_top) (measure_mono (fun x hx => hJJK hx))
  have hJ0 : μ J ≠ 0 := (hJo.measure_pos μ ⟨1, J.one_mem⟩).ne'
  have hinfJ : GinfC V ≤ J := by
    show GinfC V ≤ K''.comap (Lev.finE V)
    rw [GlobalTheory.Mass.Levels.comap_finE]
    exact le_sup_right
  have hcont : Continuous Φ := continuous_of_level V K'' hK''.1 Φ hr hc
  have hu : ∀ x : GA D V, ∃! c, ∃ γ ∈ GQ V, ∃ k ∈ J, x = γ * z c * k :=
    existsUnique_doubleCoset (finHom V).rangeRestrict (GQ V) (levelFin V K'') y hy z hz
  have hs : ∀ c, (classGroupAt V K'' (y c) : Set (GQ V)) = {γ : GQ V | (z c)⁻¹ * (γ : GA D V) * z c ∈ J} := by
    intro c
    ext γ
    rw [SetLike.mem_coe, ← hz c, mem_classGroupAt]
    rfl
  have hfinΓ : ∀ c, {γ : GQ V | (z c)⁻¹ * (γ : GA D V) * z c ∈ J}.Finite := fun c =>
    GlobalTheory.InnerClassSum.finite_stab_of_measure μ (GQ V) J hμ.2 hJ0 hJtop (z c)
  have him : ∀ c, {γ : GA D V | γ ∈ GQ V ∧ (z c)⁻¹ * γ * z c ∈ J} =
      Subtype.val '' {γ : GQ V | (z c)⁻¹ * (γ : GA D V) * z c ∈ J} := by
    intro c
    ext γ
    simp only [Set.mem_setOf_eq, Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
    exact ⟨fun h => ⟨h.1, h.2⟩, fun ⟨h, h'⟩ => ⟨h, h'⟩⟩
  have hfin : ∀ c, {γ : GA D V | γ ∈ GQ V ∧ (z c)⁻¹ * γ * z c ∈ J}.Finite := fun c =>
    him c ▸ (hfinΓ c).image _
  have hdec : ∀ k ∈ J, ∃ k' ∈ Lev.levA V K'', ∃ w : GinfC V, k = k' * (GinfC V).subtype w := fun k hk =>
    ⟨finPart V k, finPart_mem_levA V hk, ⟨realPart V k, realPart_mem V k⟩, (finPart_mul_realPart V k).symm⟩
  have hcomm : ∀ k ∈ Lev.levA V K'', ∀ w : GinfC V, k * (GinfC V).subtype w = (GinfC V).subtype w * k :=
    fun k hk w => (Eqv.Act.comm_inf_fin w.2 (Subgroup.mem_inf.1 hk).1).symm
  have hrt : ∀ w : GinfC V, MeasurePreserving (· * (GinfC V).subtype w) μ μ := fun w =>
    measurePreserving_mul_right_of_mem μ J hJo hJ0 hJtop (hinfJ w.2)
  obtain ⟨-, heq⟩ := integral_eq_sum_avg (GA D V) μ (GQ V) J (Lev.levA V K'') 𝓕 hμ.2 hJo hJtop (GinfC V) κ
    (GinfC V).subtype continuous_subtype_val hrt hdec hcomm (FinCl V K'') z hu hfin Φ hcont hl hr
  rw [heq, Finset.mul_sum, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hcard : Nat.card (classGroupAt V K'' (y c)) = gamOrd V K'' (Quotient.out c) := by
    show Nat.card (Bridge.stab (Bridge.ratF V) (levelFin V K'') (e (Quotient.out c))) = _
    rw [stab_transfer _ _ e he _ _ hJe]
    exact card_stab V K'' _
  have hcard' : ((classGroupAt V K'' (y c) : Set (GQ V))).ncard = gamOrd V K'' (Quotient.out c) :=
    (Nat.card_coe_set_eq _).symm.trans hcard
  rw [him, Set.ncard_image_of_injective _ Subtype.val_injective, ← hs, hcard', div_eq_mul_inv, mul_assoc]
  rfl

end GlobalTheory.DefiniteClassReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIntegralOfPowEqOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section
namespace GlobalTheory.RowEx

theorem exists_nf_of_finite (S : Set ℂ) (hS : S.Finite) (hi : ∀ z ∈ S, IsIntegral ℚ z) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ S ⊆ Set.range (algebraMap M ℂ) := by
  haveI : Finite S := hS.to_subtype
  refine ⟨IntermediateField.adjoin ℚ S, IntermediateField.finiteDimensional_adjoin hi, fun z hz => ?_⟩
  exact ⟨⟨z, IntermediateField.subset_adjoin ℚ S hz⟩, rfl⟩

theorem rootsOne_finite {n : ℕ} (hn : 0 < n) : {z : ℂ | z ^ n = 1}.Finite :=
  (Polynomial.nthRoots n (1 : ℂ)).toFinset.finite_toSet.subset fun z hz => by
    simpa [Polynomial.mem_nthRoots hn] using hz

theorem isIntegral_of_pow_eq_one {n : ℕ} (hn : 0 < n) {z : ℂ} (hz : z ^ n = 1) : IsIntegral ℚ z :=
  ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C _ hn.ne', by simp [hz]⟩

theorem isIntegral_sqrt_nat (k : ℕ) : IsIntegral ℚ ((Real.sqrt k : ℝ) : ℂ) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C ((k : ℚ)), Polynomial.monic_X_pow_sub_C _ two_ne_zero, ?_⟩
  have h0 : ((Real.sqrt k : ℝ) : ℂ) ^ 2 = (k : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  simp [Polynomial.eval₂_sub, h0]

end GlobalTheory.RowEx
end

namespace GlobalTheory.RowEx

theorem nfRoot : NFRoot := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hs ch _ _ => ?_⟩⟩
  haveI : Finite T := hs.fin
  classical
  set G := ch.G
  set S := ch.S.toGridChoice
  have hN : ∀ w : Pl D.host.E, 0 < Ideal.absNorm w.asIdeal ^ depthAt G w := fun w =>
    pow_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 w.ne_bot)) _
  let P : Set (Pl D.host.E) := {w | w ∈ S.PA ∨ ∃ t, w ∈ locPl G t}
  have hP : P.Finite := by
    refine ((S.PA.finite_toSet).union (Set.finite_iUnion fun t => (locPl G t).finite_toSet)).subset ?_
    rintro w (hw | ⟨t, hw⟩)
    · exact Or.inl hw
    · exact Or.inr (Set.mem_iUnion.2 ⟨t, hw⟩)
  let Q : Set (Pl D.host.E) := ⋃ t, (locPl G t : Set (Pl D.host.E))
  have hQ : Q.Finite := Set.finite_iUnion fun t => (locPl G t).finite_toSet
  let X : Set ℂ := {z | z ^ 8 = 1} ∪ (⋃ w ∈ Q, {z : ℂ | z ^ (Ideal.absNorm w.asIdeal ^ depthAt G w) = 1}) ∪
    (fun w : Pl D.host.E => ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ)) '' P
  have hX : X.Finite :=
    ((rootsOne_finite (by norm_num)).union (hQ.biUnion fun w _ => rootsOne_finite (hN w))).union (hP.image _)
  have hi : ∀ z ∈ X, IsIntegral ℚ z := by
    rintro z ((hz | hz) | ⟨w, -, rfl⟩)
    · exact isIntegral_of_pow_eq_one (by norm_num) hz
    · obtain ⟨w, -, hz⟩ := Set.mem_iUnion₂.1 hz
      exact isIntegral_of_pow_eq_one (hN w) hz
    · exact isIntegral_sqrt_nat _
  obtain ⟨M, hM, hMX⟩ := exists_nf_of_finite X hX hi
  refine ⟨M, hM, fun z hz => hMX (Or.inl (Or.inl hz)), fun t w hw z hz => hMX (Or.inl (Or.inr ?_)), fun w hw => hMX (Or.inr ⟨w, hw, rfl⟩)⟩
  exact Set.mem_iUnion₂.2 ⟨w, Set.mem_iUnion.2 ⟨t, hw⟩, hz⟩

end GlobalTheory.RowEx
end

