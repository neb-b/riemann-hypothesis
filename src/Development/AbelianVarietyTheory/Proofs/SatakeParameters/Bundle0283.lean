module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0340
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KmapOfOkOfVecP
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0056
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.Bundle0001
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceEqZeroOffSubgroupOfSelfTwist
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SelfTwWeak

theorem trace_of_charpoly {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (N : Matrix (Fin a) (Fin a) (Qbar l))
    (S : Multiset ℂ) (h : N.charpoly.map ι.toRingHom = (S.map fun b => X - C b).prod) : ι N.trace = S.sum := by
  have h1 := congrArg Polynomial.nextCoeff h
  rw [nextCoeff_map ι.injective, multiset_prod_X_sub_C_nextCoeff] at h1
  rw [Matrix.trace_eq_neg_charpoly_nextCoeff, map_neg]
  change -(ι.toRingHom N.charpoly.nextCoeff) = _
  rw [h1, neg_neg]

theorem algSat_mul (n q : ℕ) (B : Multiset ℂˣ) (e : ℂˣ) :
    (UpperTheory.V.Af.algSat n q (B.map (· * e))).sum = (e : ℂ) * (UpperTheory.V.Af.algSat n q B).sum := by
  simp only [UpperTheory.V.Af.algSat]
  simp
  simp only [mul_assoc, Multiset.sum_map_mul_left, Multiset.sum_map_mul_right]
  ring

theorem selfTw_mul_trace_inv (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω]
    [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : CuspSub K a)
    (r : G K Ω →* GL (Fin a) (Qbar l)) (hr : Weak π ι r) (η : HChar K)
    (hη : UpperTheory.V.Published.SelfTw (CG.mk π).HasSat η) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ∀ (A : ValuationSubring Ω) (σ : G K Ω),
      IsPlaceOver A v → IsFrob A (normV v) σ →
        (η.val v : ℂ) * ι (r σ⁻¹).val.trace = ι (r σ⁻¹).val.trace := by
  obtain ⟨-, -, hev⟩ := hr
  filter_upwards [hev, hη] with v hv1 hv2 A σ hA hσ
  obtain ⟨B, hB, hF⟩ := hv1
  obtain ⟨-, B', hB', hBη⟩ := hv2
  have hBB : B' = B := hB'.unique hB
  subst hBB
  have ht := trace_of_charpoly ι _ _ ((hF A hA).2 σ hσ)
  rw [ht]
  conv_rhs => rw [← hBη]
  rw [algSat_mul]

theorem ne_one_of_moves (Ω : Type) [Field Ω] (K : Type) [Field K] [Algebra K Ω] (M : Type) [Field M] [Algebra M Ω]
    [Algebra K M] [IsScalarTower K M Ω] [FiniteDimensional K M] [IsGalois K M] (hp : (Module.finrank K M).Prime)
    (χ : G K Ω →* ℂˣ) (hne : χ ≠ 1)
    (h3 : ∀ g : G K Ω, (∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) → χ g = 1) (g : G K Ω)
    (hg : ∃ x : M, g (algebraMap M Ω x) ≠ algebraMap M Ω x) : χ g ≠ 1 := by
  classical
  let ρ : G K Ω →* (M ≃ₐ[K] M) := AlgEquiv.restrictNormalHom M
  have hfix : ∀ k : G K Ω, ρ k = 1 → ∀ x : M, k (algebraMap M Ω x) = algebraMap M Ω x := by
    intro k hk x
    have := AlgEquiv.restrictNormal_commutes k M x
    rw [← this]
    change algebraMap M Ω (ρ k x) = _
    rw [hk]; rfl
  haveI : Fact (Nat.card (M ≃ₐ[K] M)).Prime := ⟨by
    first
      | (rw [IsGalois.card_aut_eq_finrank]; exact hp)
      | (convert hp using 1; rw [Nat.card_eq_fintype_card]; convert IsGalois.card_aut_eq_finrank K M)⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card ((χ.ker).map ρ) with hH | hH
  · intro hχg
    obtain ⟨x, hx⟩ := hg
    have : ρ g ∈ (χ.ker).map ρ := ⟨g, hχg, rfl⟩
    rw [hH, Subgroup.mem_bot] at this
    exact hx (hfix g this x)
  · exfalso
    apply hne
    ext k
    have : ρ k ∈ (χ.ker).map ρ := by rw [hH]; trivial
    obtain ⟨k', hk', hkk⟩ := this
    have h1 : χ (k * k'⁻¹) = 1 := h3 _ (hfix _ (by rw [map_mul, map_inv, hkk, mul_inv_cancel]))
    rw [map_mul, map_inv, MonoidHom.mem_ker.1 hk', inv_one, mul_one] at h1
    simp [h1]

theorem inv_moves {Ω K M : Type} [Field Ω] [Field K] [Algebra K Ω] [Field M] [Algebra M Ω] (g : G K Ω)
    (hg : ∃ x : M, g (algebraMap M Ω x) ≠ algebraMap M Ω x) : ∃ x : M, g⁻¹ (algebraMap M Ω x) ≠ algebraMap M Ω x := by
  obtain ⟨x, hx⟩ := hg
  refine ⟨x, fun h => hx ?_⟩
  have e : (g * g⁻¹) (algebraMap M Ω x) = algebraMap M Ω x := by rw [mul_inv_cancel]; rfl
  rw [AlgEquiv.mul_apply, h] at e
  exact e

theorem trace_eq_zero_of_selfTw : ∀ (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω] [IsAlgClosure K Ω] (M : Type) [Field M] [NumberField M] [IsCMField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra K M] [IsScalarTower K M Ω] [IsGalois K M], (Module.finrank K M).Prime → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : CuspSub K a) (r : G K Ω →* GL (Fin a) (Qbar l)), Weak π ι r → ∀ η : HChar K, UpperTheory.V.Published.IsNormChar M η → UpperTheory.V.Published.SelfTw (CG.mk π).HasSat η → ∀ g : G K Ω, (∃ x : M, g (algebraMap M Ω x) ≠ algebraMap M Ω x) → (r g).val.trace = 0 := by
  intro Ω _ K _ _ _ _ _ M _ _ _ _ _ _ _ _ hp l _ ι a π r hr η hη hst g hg
  obtain ⟨χ, hχo, hχ1, hχf⟩ :=
    GlobalTheory.HeckeToGal.exists_galChar_of_finite_order Ω K η (Module.finrank K M) hp.pos hη.2.1
  have hχne : χ ≠ 1 := fun h => hη.1 (hχ1 h)
  have h3 := GlobalTheory.trivial_on_ext_of_frob_eq_normChar Ω K M η hη χ hχo hχf
  have hne := ne_one_of_moves Ω K M hp χ hχne h3 g⁻¹ (inv_moves g hg)
  have h1 := selfTw_mul_trace_inv Ω K l ι a π r hr η hst
  have hcont : Continuous r := hr.1
  have hUo : IsOpen {k : G K Ω | χ k ≠ 1} := by
    have hc : IsClosed (χ.ker : Set (G K Ω)) := Subgroup.isClosed_of_isOpen _ hχo
    have : {k : G K Ω | χ k ≠ 1} = (χ.ker : Set (G K Ω))ᶜ := by ext k; simp [MonoidHom.mem_ker]
    rw [this]; exact hc.isOpen_compl
  have hT := Filter.eventually_cofinite.1 (h1.and hχf)
  have hD := GlobalTheory.frob_dense_off_finite K Ω _ hT
  have hc : Continuous fun k : G K Ω => (r k⁻¹).val.trace :=
    (Units.continuous_val.comp (hcont.comp continuous_inv)).matrix_trace
  have hZ : IsClosed {k : G K Ω | (r k⁻¹).val.trace = 0} := isClosed_eq hc continuous_const
  have hsub := hD.open_subset_closure_inter hUo hne
  have key : (r g⁻¹⁻¹).val.trace = 0 := by
    refine closure_minimal ?_ hZ hsub
    rintro σ ⟨hσU, v, hv, A, hA, hσ⟩
    simp only [Set.mem_setOf_eq, not_not] at hv
    have e1 := hv.1 A σ hA hσ
    have e2 := hv.2 A σ hA hσ
    have hv1 : (η.val v : ℂ) ≠ 1 := by
      intro h; apply hσU; rw [e2]; exact Units.val_eq_one.1 h
    have : ι (r σ⁻¹).val.trace = 0 := by
      have h0 : ((η.val v : ℂ) - 1) * ι (r σ⁻¹).val.trace = 0 := by rw [sub_mul, e1, one_mul, sub_self]
      exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hv1)
    exact (map_eq_zero_iff ι ι.injective).1 this
  rwa [inv_inv] at key

end GlobalTheory.SelfTwWeak

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueKernelJetsMulDetCharactersMemCoefficientFiel
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 800000

namespace GlobalTheory.Mem.Col2.TC

open GlobalTheory.LvT.Built.KMap

theorem rho_jet_mem : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ColIn.JetsIn I → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i < B.R.m → ∀ (c : (I.stp u a i).Cl) (c' : (I.stp u a (i + 1)).Cl) (e : DVar B.fields.Tau (B.R.N i) (B.R.N (i + 1)) →₀ ℕ), (∀ τ, (monoDeg e τ : ℤ) = nuDeg B u i τ) → ∃ k : B.LL, B.embLL k = (I.rho u a i c.1 ((I.stp u a i).rep c) * I.rho' u a i c'.1 ((I.stp u a (i + 1)).rep c')) * jetC I.J.cD (I.th u a i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c')) e := by
  classical
  intro B X I h hP l Z hJ u a i hi c c' e he
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  obtain ⟨hLa, hE⟩ := _root_.GlobalTheory.Mem.Col2.TC.laHyp_eSmooth_true I h hP l Z a u i hi
  set p := (I.stp u a i).rep c
  set p' := (I.stp u a (i + 1)).rep c'
  have hN : IsSdLat p.1.1.deco.1.N := ⟨p.1.1.deco.2.lat, p.1.1.deco.2.uni⟩
  have hN' : IsSdLat p'.1.1.deco.1.N := ⟨p'.1.1.deco.2.lat, p'.1.1.deco.2.uni⟩
  have hA : 0 < cAof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) :=
    pow_pos (Finset.prod_pos fun P _ => qOf_pos P.1) _
  have hB : 0 < cBof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) u := GlobalTheory.MoveCompare.cBof_pos hPr _ _ _ u
  have hbox := GlobalTheory.LvT.Built.Box.inBox_xiAt B.fields (B.primes X) B.R I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) _ _ u i hX hPr
    h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) hi ⟨_, _, _, _, h.ch_tied⟩ c.1 c'.1 p p'
  set N := p.1.1.deco.1.N
  set N' := p'.1.1.deco.1.N
  set cA := cAof (Pr := B.primes X) I.sel (I.tup a) (I.cst a)
  set cB := cBof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) u
  set Ξ := xiAt (Pr := B.primes X) I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1 c'.1 p p'
  have hNfull : Submodule.IsFullLattice B.fields.E N := by
    let := hN.1
    refine { span_eq_top := ?_ }
    let W := Submodule.span B.fields.E (N : Set (Sp B.fields.E (B.R.N i)))
    change W = ⊤
    by_contra hspan
    let e : Sp B.fields.E (B.R.N i) ≃ₗ⋆[B.fields.E] Sp B.fields.E (B.R.N i) := starLinearEquiv B.fields.E
    let g : Sp B.fields.E (B.R.N i) →ₗ[B.fields.E] Module.Dual B.fields.E W :=
      (LinearMap.domRestrict' W).comp ((hStd B.fields.E (B.R.N i)).comp e.toLinearMap)
    have hdim : Module.finrank B.fields.E (Module.Dual B.fields.E W) < Module.finrank B.fields.E (Sp B.fields.E (B.R.N i)) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hspan
    obtain ⟨x, hx, hx₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    have hsmul (a : B.fields.E) : a • e x ∈ N := by
      rw [← hN.2, Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
      intro y hy
      apply hStd_mem_one_symm
      have hxy : hStd B.fields.E (B.R.N i) (e x) y = 0 :=
        congrArg (fun f : Module.Dual B.fields.E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
      simp [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hxy]
    let j : B.fields.E →ₗ[𝓞 B.fields.E] N :=
      ((LinearMap.toSpanSingleton B.fields.E _ (e x)).restrictScalars (𝓞 B.fields.E)).codRestrict N hsmul
    let : Module.Finite (𝓞 B.fields.E) N := Module.Finite.iff_fg.mpr hN.1.fg
    let : Module.Finite (𝓞 B.fields.E) B.fields.E := Module.Finite.of_injective j fun a b hab =>
      smul_left_injective B.fields.E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField B.fields.E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 B.fields.E) B.fields.E) (Field.toIsField B.fields.E))
  have hth := GlobalTheory.latSum_thInd_eq_thC B.fields I.A _ _ (I.Sb a u) N N' cA cB (fun x => I.A.σ₀ (Ξ x))
    (indTieD_of_la I.A _ _ _ _ (Nat.mul_pos hA hB) hLa) hN hN' hA hB (volC_pos_of_laHyp I.A _ _ _ hLa hN hN')
    (GlobalTheory.finite_divLat_quot_mulLat_homAt _ _ _ _ _ _ _ _ hNfull hN'.1 hA hB) (fun x hx => hbox.1 x ((map_ne_zero _).1 hx))
    (fun x y hy => congrArg I.A.σ₀ (hbox.2 x y hy))
  have hfin := GlobalTheory.finite_divLat_quot_mulLat_homAt _ _ _ (I.Sb a u) N N' cA cB hNfull hN'.1 hA hB
  let _ := @Fintype.ofFinite _ hfin
  rw [show I.th u a i c.1 c'.1 p p' = fun z => _ from funext fun z => (hth z).symm]
  unfold latSum
  simp only [finsum_eq_sum_of_fintype]
  set r := Function.surjInv (Submodule.Quotient.mk_surjective
    ((Formalism.L2.Col.mulLat cB (homAt (I.Sb a u) N N')).comap (divLat cA (homAt (I.Sb a u) N N')).subtype))
  have hs : ∀ q (k : ℕ), ContDiff ℂ k (I.A.thInd (I.Sb a u) N N' cB (r q)) := fun q =>
    indSmooth_of I.A _ _ (I.Sb a u) (cA * cB) hE N N' cB (r q) ⟨hN, hN', hB, Dvd.intro_left _ rfl, divLat_mul_of cA cB _ (r q).2⟩
  rw [show I.J.cD = I.A.cD from rfl, jetC_sum _ _ _ hs]
  have hr := rhoIs I h a u hi c.1 p c'.1 p'
  rw [show I.rho u a i c.1 p * I.rho' u a i c'.1 p' = _ from hr]
  have hσ : (ColIn.A I).σ₀ = B.embLL := rfl
  rw [hσ]
  apply RingHom.mem_fieldRange.1
  rw [mul_assoc, Finset.mul_sum]
  refine Subfield.mul_mem _ (RingHom.mem_fieldRange_self _ _) (Subfield.sum_mem _ fun q _ => ?_)
  obtain ⟨y, hy⟩ := hJ.exists_eq (a := a) (u := u) (N := N) (N' := N') (c := cB) (x := (r q).1) (e := e) hi
    ⟨hN, hN', hB, Dvd.intro_left _ rfl, divLat_mul_of cA cB _ (r q).2⟩ he
  rw [mul_left_comm]
  refine Subfield.mul_mem _ (RingHom.mem_fieldRange_self _ _) ?_
  exact ⟨y, hy⟩

end GlobalTheory.Mem.Col2.TC
end

