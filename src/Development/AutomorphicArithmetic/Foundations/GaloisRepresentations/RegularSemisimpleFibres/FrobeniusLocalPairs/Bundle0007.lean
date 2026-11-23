module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.GlobOf
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DZA UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

private lemma galOf_mul' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {A B : Type*} [CommRing A] [Algebra F A] [CommRing B] [Algebra E B] (e : TensorProduct F E A ≃ₐ[E] B)
    (a b : E ≃ₐ[F] E) (y : B) :
    PositivityTheory.Rg.Tf.Geo.galOf e (a * b) y = PositivityTheory.Rg.Tf.Geo.galOf e a (PositivityTheory.Rg.Tf.Geo.galOf e b y) := by
  have h : ∀ z : TensorProduct F E A,
      Algebra.TensorProduct.map ((a * b : E ≃ₐ[F] E) : E →ₐ[F] E) (AlgHom.id F A) z =
        Algebra.TensorProduct.map (a : E →ₐ[F] E) (AlgHom.id F A)
          (Algebra.TensorProduct.map (b : E →ₐ[F] E) (AlgHom.id F A) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x c => simp
    | add x c hx hc => simp only [map_add (f := _), hx, hc]
  simp [PositivityTheory.Rg.Tf.Geo.galOf, h]

private lemma galOf_one' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {A B : Type*} [CommRing A] [Algebra F A] [CommRing B] [Algebra E B] (e : TensorProduct F E A ≃ₐ[E] B)
    (y : B) : PositivityTheory.Rg.Tf.Geo.galOf e (1 : E ≃ₐ[F] E) y = y := by
  have h : ∀ z : TensorProduct F E A,
      Algebra.TensorProduct.map ((1 : E ≃ₐ[F] E) : E →ₐ[F] E) (AlgHom.id F A) z = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x c => simp
    | add x c hx hc => simp only [map_add (f := _), hx, hc]
  simp [PositivityTheory.Rg.Tf.Geo.galOf, h]

private lemma galFin_mul' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (a b : E ≃ₐ[F] E) (v : Pl F) (y : CompletionsOver E v) :
    galFin (a * b) v y = galFin a v (galFin b v y) := galOf_mul' _ a b y

private lemma galFin_one' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : Pl F) (y : CompletionsOver E v) : galFin (1 : E ≃ₐ[F] E) v y = y := galOf_one' _ y

theorem globOf : GlobOf := by
  intro F E _ _ _ _ _ _ hp v w hw
  have hs := sum_finrank_eq E v
  rw [Fintype.sum_eq_single w (fun w' h => (h (hw w')).elim)] at hs
  intro alg hcomp
  have hdeg : Module.finrank (HeightOneSpectrum.adicCompletion F v) (HeightOneSpectrum.adicCompletion E w.1)
      = Module.finrank F E := by
    convert hs using 2
    congr 1
    first
    | exact Algebra.algebra_ext _ _ (fun x => (hcomp x).symm)
    | exact Algebra.algebra_ext _ _ (fun x => hcomp x)
  have hp2 := hp.two_le
  haveI : FiniteDimensional (HeightOneSpectrum.adicCompletion F v) (HeightOneSpectrum.adicCompletion E w.1) :=
    Module.finite_of_finrank_pos (by omega)
  let ψ : CompletionsOver E v ≃+* HeightOneSpectrum.adicCompletion E w.1 :=
    RingEquiv.ofBijective (Pi.evalRingHom (fun w' : PlacesOver E v => HeightOneSpectrum.adicCompletion E w'.1) w)
      ⟨fun y₁ y₂ h => funext fun w' => by
          obtain rfl := hw w'
          exact h,
        fun z => ⟨fun w' => by
          rw [hw w']
          exact z, rfl⟩⟩
  have hx : ∀ (σ : Gal(E/F)) (x : E),
      galFin σ v (algebraMap E (CompletionsOver E v) x) = algebraMap E (CompletionsOver E v) (σ x) := by
    intro σ x
    have e1 : ∀ z : E, algebraMap E (CompletionsOver E v) z =
        tensorEquiv' E v (z ⊗ₜ[F] (1 : HeightOneSpectrum.adicCompletion F v)) := by
      intro z
      rw [tensorEquiv'_tmul, map_one, mul_one]
    rw [e1, e1]
    show tensorEquiv' E v (Algebra.TensorProduct.map ((σ : E ≃ₐ[F] E) : E →ₐ[F] E) (AlgHom.id F _)
      ((tensorEquiv' E v).symm (tensorEquiv' E v (x ⊗ₜ[F] (1 : HeightOneSpectrum.adicCompletion F v))))) = _
    rw [AlgEquiv.symm_apply_apply, Algebra.TensorProduct.map_tmul]
    rfl
  have halg : ∀ (σ : Gal(E/F)) (r : HeightOneSpectrum.adicCompletion F v),
      galFin σ v (algebraMap _ (CompletionsOver E v) r) = algebraMap _ (CompletionsOver E v) r := by
    intro σ r
    have e1 : algebraMap _ (CompletionsOver E v) r = tensorEquiv' E v ((1 : E) ⊗ₜ[F] r) := by
      rw [tensorEquiv'_tmul, map_one, one_mul]
    rw [e1]
    show tensorEquiv' E v (Algebra.TensorProduct.map ((σ : E ≃ₐ[F] E) : E →ₐ[F] E) (AlgHom.id F _)
      ((tensorEquiv' E v).symm (tensorEquiv' E v ((1 : E) ⊗ₜ[F] r)))) = _
    rw [AlgEquiv.symm_apply_apply, Algebra.TensorProduct.map_tmul, map_one]
    rfl
  have hψalg : ∀ r : HeightOneSpectrum.adicCompletion F v,
      ψ.symm (algebraMap _ (HeightOneSpectrum.adicCompletion E w.1) r) = algebraMap _ (CompletionsOver E v) r := by
    intro r
    apply ψ.injective
    rw [RingEquiv.apply_symm_apply]
    exact (hcomp r).symm
  let φ : Gal(E/F) →* Gal(HeightOneSpectrum.adicCompletion E w.1/HeightOneSpectrum.adicCompletion F v) :=
    { toFun := fun σ =>
        { toFun := fun z => ψ (galFin σ v (ψ.symm z))
          invFun := fun z => ψ (galFin σ⁻¹ v (ψ.symm z))
          left_inv := fun z => by
            show ψ (galFin σ⁻¹ v (ψ.symm (ψ (galFin σ v (ψ.symm z))))) = z
            rw [RingEquiv.symm_apply_apply, ← galFin_mul', inv_mul_cancel, galFin_one',
              RingEquiv.apply_symm_apply]
          right_inv := fun z => by
            show ψ (galFin σ v (ψ.symm (ψ (galFin σ⁻¹ v (ψ.symm z))))) = z
            rw [RingEquiv.symm_apply_apply, ← galFin_mul', mul_inv_cancel, galFin_one',
              RingEquiv.apply_symm_apply]
          map_mul' := fun a b => by simp only [map_mul]
          map_add' := fun a b => by simp only [map_add (f := _)]
          commutes' := fun r => by
            show ψ (galFin σ v (ψ.symm (algebraMap _ _ r))) = _
            rw [hψalg, halg]
            exact hcomp r }
      map_one' := by
        apply AlgEquiv.ext
        intro z
        show ψ (galFin 1 v (ψ.symm z)) = z
        rw [galFin_one', RingEquiv.apply_symm_apply]
      map_mul' := by
        intro a b
        apply AlgEquiv.ext
        intro z
        show ψ (galFin (a * b) v (ψ.symm z)) = ψ (galFin a v (ψ.symm (ψ (galFin b v (ψ.symm z)))))
        rw [RingEquiv.symm_apply_apply, galFin_mul'] }
  haveI : Nontrivial (CompletionsOver E v) := ψ.toEquiv.nontrivial
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    apply AlgEquiv.ext
    intro x
    have h1 : φ σ (ψ (algebraMap E (CompletionsOver E v) x)) = ψ (algebraMap E (CompletionsOver E v) x) := by
      rw [hσ]
      rfl
    have h2 : φ σ (ψ (algebraMap E (CompletionsOver E v) x)) = ψ (algebraMap E (CompletionsOver E v) (σ x)) := by
      show ψ (galFin σ v (ψ.symm (ψ _))) = _
      rw [RingEquiv.symm_apply_apply, hx]
    exact (algebraMap E (CompletionsOver E v)).injective (ψ.injective (h2.symm.trans h1))
  have hbij : Function.Bijective φ := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, le_antisymm (Fintype.card_le_of_injective _ hinj) ?_⟩
    have c1 := AlgEquiv.card_le (F := HeightOneSpectrum.adicCompletion F v)
      (K := HeightOneSpectrum.adicCompletion E w.1)
    have c2 := IsGalois.card_aut_eq_finrank F E
    simp only [Fintype.card_eq_nat_card] at c1 c2 ⊢
    omega
  refine ⟨?_, hdeg, ?_⟩
  · intro hsplit
    have h1 : Module.finrank (HeightOneSpectrum.adicCompletion F v) (HeightOneSpectrum.adicCompletion E w.1) = 1 := by
      rw [finrank_eq_one_iff_of_nonzero' (1 : HeightOneSpectrum.adicCompletion E w.1) one_ne_zero]
      intro z
      obtain ⟨c, hc⟩ := hsplit w z
      exact ⟨c, by rw [Algebra.smul_def, mul_one, ← hcomp, hc]⟩
    omega
  · intro s hs
    obtain ⟨σ, hσ⟩ := hbij.2 s
    refine ⟨σ, ?_, ?_⟩
    · intro τ
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hs (φ τ))
      refine Subgroup.mem_zpowers_iff.2 ⟨n, hinj ?_⟩
      rw [map_zpow, hσ, hn]
    · intro y
      rw [← hσ]
      show _ = ψ (galFin σ v (ψ.symm (ψ y)))
      rw [RingEquiv.symm_apply_apply]
      rfl

end UpperTheory.Gal.InertialTypesAlt.L
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.InflFacts
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DZA UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

section Alg

variable {k : Type} [Field k] [ValuativeRel k] {F₀ : Type} [Field F₀] {n : ℕ}

private theorem incl_inj :
    Function.Injective (GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k)) := fun a b h =>
  Units.ext <| Matrix.ext fun i j => Subtype.ext
    (congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i j) h)

private theorem infl_incl (rd : 𝒪[k] →+* F₀) (fb : GL (Fin n) F₀ → ℂ) (y : GL (Fin n) 𝒪[k]) :
    infl rd fb (GeneralLinearGroup.map (algebraMap 𝒪[k] k) y) = fb (GeneralLinearGroup.map rd y) := by
  have h : ∃ y' : GL (Fin n) 𝒪[k], GeneralLinearGroup.map (algebraMap 𝒪[k] k) y' =
      GeneralLinearGroup.map (algebraMap 𝒪[k] k) y := ⟨y, rfl⟩
  unfold infl
  rw [dite_eq_left h, incl_inj h.choose_spec]

private theorem infl_not_mem (rd : 𝒪[k] →+* F₀) (fb : GL (Fin n) F₀ → ℂ) {x : GL (Fin n) k}
    (hx : x ∉ KO k n) : infl rd fb x = 0 :=
  dif_neg hx

private theorem principal_congruence_le_maximal_compact (rd : 𝒪[k] →+* F₀) : K1 rd n ≤ KO k n := by
  rintro _ ⟨y, -, rfl⟩
  exact ⟨y, rfl⟩

private theorem infl_left (rd : 𝒪[k] →+* F₀) (fb : GL (Fin n) F₀ → ℂ) {c : GL (Fin n) k}
    (hc : c ∈ K1 rd n) (x : GL (Fin n) k) : infl rd fb (c * x) = infl rd fb x := by
  by_cases hx : x ∈ KO k n
  · obtain ⟨u, hu, rfl⟩ := hc
    obtain ⟨y, rfl⟩ := hx
    rw [← map_mul, infl_incl, infl_incl, map_mul, MonoidHom.mem_ker.1 hu, one_mul]
  · rw [infl_not_mem rd fb hx, infl_not_mem rd fb]
    exact fun h => hx (by simpa using (KO k n).mul_mem ((KO k n).inv_mem (principal_congruence_le_maximal_compact rd hc)) h)

private theorem infl_right (rd : 𝒪[k] →+* F₀) (fb : GL (Fin n) F₀ → ℂ) {c : GL (Fin n) k}
    (hc : c ∈ K1 rd n) (x : GL (Fin n) k) : infl rd fb (x * c) = infl rd fb x := by
  by_cases hx : x ∈ KO k n
  · obtain ⟨u, hu, rfl⟩ := hc
    obtain ⟨y, rfl⟩ := hx
    rw [← map_mul, infl_incl, infl_incl, map_mul, MonoidHom.mem_ker.1 hu, mul_one]
  · rw [infl_not_mem rd fb hx, infl_not_mem rd fb]
    exact fun h => hx (by simpa using (KO k n).mul_mem h ((KO k n).inv_mem (principal_congruence_le_maximal_compact rd hc)))

private theorem rd_eq_zero (rd : 𝒪[k] →+* F₀) (hrd : Function.Surjective rd) (x : 𝒪[k])
    (hx : valuation k (x : k) < 1) : rd x = 0 := by
  by_contra h0
  obtain ⟨y, hy⟩ := hrd (rd x)⁻¹
  have hxy : rd (1 - x * y) = 0 := by
    rw [map_sub, map_mul, hy, mul_inv_cancel₀ h0, map_one, sub_self]
  have hyle : valuation k (y : k) ≤ 1 := y.2
  have hlt : valuation k ((x * y : 𝒪[k]) : k) < 1 := by
    rw [Subring.coe_mul, map_mul]
    exact mul_lt_one_of_lt_of_le hx hyle
  have hval : valuation k ((1 - x * y : 𝒪[k]) : k) = 1 := by
    have : ((1 - x * y : 𝒪[k]) : k) = 1 - ((x * y : 𝒪[k]) : k) := by push_cast; ring
    rw [this, Valuation.map_one_sub_of_lt _ hlt]
  set u : 𝒪[k] := 1 - x * y with hu
  have hu0 : (u : k) ≠ 0 := fun h => by rw [h, map_zero] at hval; exact zero_ne_one hval
  have hinv : valuation k (u : k)⁻¹ ≤ 1 := by rw [map_inv₀, hval, inv_one]
  have hone : u * ⟨(u : k)⁻¹, hinv⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hu0)
  have := congrArg rd hone
  rw [map_mul, hxy, zero_mul, map_one] at this
  exact zero_ne_one this

end Alg

theorem inflFacts :
    UpperTheory.Gal.InertialTypesAlt.L.InflFacts := by
  intro k _ _ _ _ F₀ _ _ rd hrd n
  have hKO : KO k n = GroundTheory.Automorphic.GLnLocal.integralGL k n := rfl
  have hU : KO k n = PositivityTheory.Rg.Tf.Loc.unitGL k := rfl
  have hopenKO : IsOpen (KO k n : Set (GL (Fin n) k)) := by
    rw [hKO]; exact GroundTheory.Automorphic.GLnLocal.isOpen_integralGL k n
  have hcompKO : IsCompact (KO k n : Set (GL (Fin n) k)) := by
    rw [hKO]; exact GroundTheory.Automorphic.GLnLocal.isCompact_integralGL k n
  obtain ⟨r, hr0, hr1⟩ : ∃ r : ValueGroupWithZero k, 0 < r ∧ r < 1 := by
    obtain ⟨γ, h0, h1⟩ := ValuativeRel.IsNontrivial.condition (R := k)
    rcases lt_or_gt_of_ne h1 with h | h
    · exact ⟨γ, zero_lt_iff.2 h0, h⟩
    · exact ⟨γ⁻¹, inv_pos.2 (zero_lt_iff.2 h0), inv_lt_one_of_one_lt₀ h⟩
  obtain ⟨B, hB, hBo, -⟩ := UpperTheory.ConvolutionTheory.Loc.ballSub k n r hr0 hr1
  have hent : ∀ g ∈ B, ∀ i j, valuation k ((g : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
    intro g hg i j
    have hb : valuation k ((g : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j) ≤ r := by
      have : g ∈ (B : Set (GL (Fin n) k)) := hg
      rw [hB] at this
      exact this i j
    have h1 : valuation k ((1 : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
      rw [Matrix.one_apply]; split_ifs <;> simp
    rw [← sub_add_cancel ((g : Matrix (Fin n) (Fin n) k) i j) ((1 : Matrix (Fin n) (Fin n) k) i j)]
    exact Valuation.map_add_le _ (hb.trans hr1.le) h1
  have hBK : B ≤ K1 rd n := by
    intro g hg
    have hgO : g ∈ GroundTheory.Automorphic.GLnLocal.integralGL k n :=
      (GroundTheory.Automorphic.GLnLocal.mem_integralGL_iff k n).2 ⟨hent g hg, hent _ (B.inv_mem hg)⟩
    obtain ⟨y, rfl⟩ : g ∈ KO k n := hgO
    refine ⟨y, ?_, rfl⟩
    change GeneralLinearGroup.map rd y = 1
    refine Units.ext (Matrix.ext fun i j => ?_)
    have hb : valuation k (((GeneralLinearGroup.map (algebraMap 𝒪[k] k) y : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j -
        (1 : Matrix (Fin n) (Fin n) k) i j) ≤ r := by
      have : GeneralLinearGroup.map (algebraMap 𝒪[k] k) y ∈ (B : Set (GL (Fin n) k)) := hg
      rw [hB] at this
      exact this i j
    have h0 := rd_eq_zero rd hrd ((y : Matrix (Fin n) (Fin n) 𝒪[k]) i j - (1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j) (by
      refine lt_of_le_of_lt (le_of_eq ?_) (hb.trans_lt hr1)
      congr 1
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij] <;> rfl)
    rw [map_sub, sub_eq_zero] at h0
    simp only [GeneralLinearGroup.map_apply, Units.val_one]
    rw [h0]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hopen : IsOpen (K1 rd n : Set (GL (Fin n) k)) := Subgroup.isOpen_mono hBK hBo
  have hclosed : IsClosed (K1 rd n : Set (GL (Fin n) k)) := Subgroup.isClosed_of_isOpen _ hopen
  have hcomp : IsCompact (K1 rd n : Set (GL (Fin n) k)) :=
    hcompKO.of_isClosed_subset hclosed (principal_congruence_le_maximal_compact rd)
  have hclosedKO : IsClosed (KO k n : Set (GL (Fin n) k)) := Subgroup.isClosed_of_isOpen _ hopenKO
  have hsupp : ∀ fb : GL (Fin n) F₀ → ℂ, HasCompactSupport (infl rd fb) := fun fb =>
    HasCompactSupport.intro' hcompKO hclosedKO fun x hx => infl_not_mem rd fb hx
  refine ⟨hU, hopen, hcomp, principal_congruence_le_maximal_compact rd, fun fb y => infl_incl rd fb y, fun fb => ⟨⟨hsupp fb, fun c hc x => ⟨infl_left rd fb hc x, infl_right rd fb hc x⟩⟩, ⟨?_, hsupp fb⟩, ?_⟩⟩
  · refine (IsLocallyConstant.iff_exists_open _).2 fun x => ⟨(fun z => x⁻¹ * z) ⁻¹' (K1 rd n : Set (GL (Fin n) k)), hopen.preimage (continuous_const.mul continuous_id), by simp [(K1 rd n).one_mem], fun z hz => ?_⟩
    have := infl_right rd fb hz x
    simpa using this
  · intro x hx
    by_contra h
    exact hx (infl_not_mem rd fb h)

end UpperTheory.Gal.InertialTypesAlt.L
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.NormOpen
section
open ValuativeRel UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.Gal.InertialTypesAlt.L.normOpen :
    UpperTheory.Gal.InertialTypesAlt.L.NormOpen := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ _ r hr0 hr1
  have hc : Continuous (algebraMap k E) := (UpperTheory.V.Z.Tf.Orb.extCont_holds k E).1
  have hS : {z : E | valuation E (z - 1) < r} ∈ nhds (algebraMap k E 1) := by
    rw [map_one]
    exact (IsValuativeTopology.hasBasis_nhds' (1 : E)).mem_of_mem hr0.ne'
  obtain ⟨γ, hγ0, hγ⟩ :=
    (IsValuativeTopology.hasBasis_nhds' (1 : k)).mem_iff.mp (hc.continuousAt.preimage_mem_nhds hS)
  set d := Module.finrank k E with hd
  have hdpos : 0 < d := Module.finrank_pos
  have hdk : (d : k) ≠ 0 := Nat.cast_ne_zero.mpr hdpos.ne'
  set δ := valuation k (d : k) with hδ
  have hδ0 : δ ≠ 0 := by simpa [hδ] using hdk
  have hδ1 : δ ≤ 1 := by
    rw [hδ]
    clear hδ hδ0 hdk hdpos hd
    induction d with
    | zero => simp
    | succ n ih =>
      push_cast
      exact ((valuation k).map_add _ _).trans (max_le ih (by simp))
  obtain ⟨t, ht0, ht1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  set ε := valuation k t with hεdef
  set μ := min γ δ
  have hμ0 : 0 < μ := lt_min (zero_lt_iff.mpr hγ0) (zero_lt_iff.mpr hδ0)
  have hε0 : 0 < ε := zero_lt_iff.mpr (by simpa [hεdef] using ht0)
  set r₂ := μ * ε
  have hr₂0 : 0 < r₂ := mul_pos hμ0 hε0
  have hr₂μ : r₂ < μ := by
    calc r₂ = μ * ε := rfl
      _ < μ * 1 := mul_lt_mul_of_pos_left ht1 hμ0
      _ = μ := mul_one μ
  have hr₂γ : r₂ < γ := hr₂μ.trans_le (min_le_left _ _)
  have hr₂δ : r₂ < δ := hr₂μ.trans_le (min_le_right _ _)
  have hr₀r₂ : r₂ * δ ≤ r₂ := by
    calc r₂ * δ ≤ r₂ * 1 := mul_le_mul_of_nonneg_left hδ1 zero_le'
      _ = r₂ := mul_one r₂
  refine ⟨r₂ * δ, mul_pos hr₂0 (zero_lt_iff.mpr hδ0), hr₀r₂.trans_lt (hr₂δ.trans_le hδ1), ?_⟩
  intro x hx
  have hmem : ∀ y : k, valuation k (y - 1) ≤ r₂ → valuation E (algebraMap k E y - 1) ≤ r := by
    intro y hy
    exact le_of_lt (hγ (lt_of_le_of_lt hy hr₂γ))
  refine ⟨hmem x (hx.trans hr₀r₂), ?_⟩
  have hg : Matrix.GeneralLinearGroup.scalar (Fin 1) x ∈ UpperTheory.ConvolutionTheory.Loc.ball 1 (r₂ * δ) := by
    intro i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    simpa [Matrix.GeneralLinearGroup.scalar] using hx
  obtain ⟨u, ⟨hu, hud⟩, -⟩ := UpperTheory.ConvolutionTheory.Loc.rootEx k 1 d r₂ hr₂δ _ hg
  have hpow : ∀ (M : Matrix (Fin 1) (Fin 1) k) (m : ℕ), (M ^ m) 0 0 = (M 0 0) ^ m := by
    intro M m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_one, ih, pow_succ]
  have hw : ((u : Matrix (Fin 1) (Fin 1) k) 0 0) ^ d = (x : k) := by
    have := congrArg (fun g : GL (Fin 1) k => (g : Matrix (Fin 1) (Fin 1) k) 0 0) hud
    simp only [Units.val_pow_eq_pow_val] at this
    rw [← hpow, this]
    simp [Matrix.GeneralLinearGroup.scalar]
  have hw1 : valuation k ((u : Matrix (Fin 1) (Fin 1) k) 0 0 - 1) ≤ r₂ := by
    simpa using hu 0 0
  have hw0 : (u : Matrix (Fin 1) (Fin 1) k) 0 0 ≠ 0 := by
    intro h
    rw [h, zero_pow hdpos.ne'] at hw
    exact x.ne_zero hw.symm
  refine ⟨Units.mk0 (algebraMap k E ((u : Matrix (Fin 1) (Fin 1) k) 0 0))
    ((map_ne_zero (algebraMap k E)).mpr hw0), hmem _ hw1, ?_⟩
  rw [Units.val_mk0, Algebra.norm_algebraMap, ← hd, hw]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.RamOne
section
open ValuativeRel PositivityTheory.Rg.Tf.Loc

private theorem ramOne (k K : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra k K] [ValuativeExtension k K] [FiniteDimensional k K] (h : IsUnramifiedLoc k K) :
    (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation k))) = 1 := by
  obtain ⟨π, hπ, hmin⟩ := h
  have hv := Valuation.integer.integers (valuation K)
  rw [← GroundTheory.LocalField.isUnramified_iff, ← GroundTheory.LocalField.map_maximalIdeal_eq_iff]
  have hπk : π ∈ 𝒪[k] := (GroundTheory.LocalField.algebraMap_mem_integer_iff k K π).1 (le_of_lt hπ)
  let p : 𝒪[k] := ⟨π, hπk⟩
  have hpK : ((algebraMap 𝒪[k] 𝒪[K] p : 𝒪[K]) : K) = algebraMap k K π := rfl
  have hp : p ∈ 𝓂[k] := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h1 := hv.one_of_isUnit (hu.map (algebraMap 𝒪[k] 𝒪[K]))
    change valuation K ((algebraMap 𝒪[k] 𝒪[K] p : 𝒪[K]) : K) = 1 at h1
    rw [hpK] at h1
    exact (ne_of_lt hπ) h1
  apply le_antisymm
  · exact Ideal.map_le_iff_le_comap.2 (fun x hx => by
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact ((IsLocalRing.mem_maximalIdeal x).1 hx) (isUnit_of_map_unit _ _ hu))
  · intro x hx
    have hxlt : valuation K (x : K) < 1 := by
      by_contra hge
      have heq : valuation K (x : K) = 1 := le_antisymm x.2 (not_lt.1 hge)
      exact ((IsLocalRing.mem_maximalIdeal x).1 hx) (hv.isUnit_of_one' heq)
    have hle := hmin (x : K) hxlt
    rw [← hpK] at hle
    obtain ⟨z, hz⟩ := hv.dvd_of_le (x := x) (y := algebraMap 𝒪[k] 𝒪[K] p) hle
    rw [hz]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hp)

theorem UpperTheory.Gal.InertialTypesAlt.L.resEx :
    UpperTheory.Gal.InertialTypesAlt.L.ResEx := by
  intro k K _ _ _ _ _ _ _ _ _ _ _ _ hu
  have h1 := ramOne k K hu
  letI : Fintype 𝓀[k] := Fintype.ofFinite _
  letI : Fintype 𝓀[K] := Fintype.ofFinite _
  refine ⟨𝓀[k], 𝓀[K], inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    IsLocalRing.residue _, IsLocalRing.residue _, GroundTheory.LocalField.frobenius k K h1,
    GroundTheory.LocalField.residueAlgEquiv k K (GroundTheory.LocalField.frobenius k K h1), ?_⟩
  refine ⟨?_, IsLocalRing.residue_surjective, IsLocalRing.residue_surjective, ?_, ?_, ?_⟩
  · rw [← GroundTheory.LocalField.residueDegree_eq_finrank,
      GroundTheory.LocalField.residueDegree_eq_finrank_of_unramified k K h1]
  · intro x y h
    have e : y = algebraMap 𝒪[k] 𝒪[K] x := Subtype.ext h
    rw [e]
    rfl
  · intro x y h
    have e : y = GroundTheory.LocalField.integerAlgEquiv k K (GroundTheory.LocalField.frobenius k K h1) x :=
      Subtype.ext h
    rw [e, GroundTheory.LocalField.residueAlgEquiv_residue]
  · intro z
    rw [GroundTheory.LocalField.residueAlgEquiv_frobenius_apply, Fintype.card_eq_nat_card]
end

