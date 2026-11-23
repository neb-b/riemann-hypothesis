module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0813
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0821
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0838
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0535
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0724
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0760
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0726
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0792
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0729
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0736
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0730
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0794
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0775
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0734

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerMassNeZeroOfMemSupport
section
open GlobalTheory.LKCount

namespace GlobalTheory

theorem massC_ne_zero_of_support {G : Type} [Group G] (Γ' T K : Subgroup G) (F : G → ℂ) (hΓT : Γ' ≤ T)
    (hF : ∀ t ∈ T, ∀ x, ∀ k ∈ K, F (t * x * k) = F x)
    (hfin : ∀ x : G, ((Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G).Finite)
    (hsupp : {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0}.Finite)
    (y : G) (hy : F y ≠ 0) :
    massC Γ' T (T ⊓ K.map (MulAut.conj y).toMonoidHom) ≠ 0 := by
  have memconj : ∀ (L : Subgroup G) (a x : G), x ∈ L.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * x * a ∈ L := by
    intro L a x
    rw [Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply]
  have memconjT : ∀ (L : Subgroup T) (a x : T), x ∈ L.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * x * a ∈ L := by
    intro L a x
    rw [Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply]
  set C := T ⊓ K.map (MulAut.conj y).toMonoidHom with hC
  set A : Subgroup T := Γ'.subgroupOf T
  set B : Subgroup T := C.subgroupOf T

  let φ : DoubleCoset.Quotient (A : Set T) (B : Set T) → DoubleCoset.Quotient (Γ' : Set G) (K : Set G) :=
    fun q => DoubleCoset.mk Γ' K (((Quotient.out q : T) : G) * y)
  have hφS : ∀ q, φ q ∈ {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0} := by
    intro q
    show F (Quotient.out (DoubleCoset.mk Γ' K (((Quotient.out q : T) : G) * y))) ≠ 0
    obtain ⟨h, hh, k, hk, he⟩ := DoubleCoset.mk_out_eq_mul Γ' K (((Quotient.out q : T) : G) * y)
    rw [he, hF h (hΓT hh) _ k hk]
    have := hF ((Quotient.out q : T) : G) (Quotient.out q).2 y 1 K.one_mem
    rw [mul_one] at this
    rw [this]; exact hy
  have hφinj : Function.Injective φ := by
    intro q1 q2 h12
    rw [← DoubleCoset.out_eq' (H := A) (K := B) q1, ← DoubleCoset.out_eq' (H := A) (K := B) q2]
    obtain ⟨g, hg, k, hk, he⟩ := (@DoubleCoset.eq _ _ Γ' K _ _).1 h12
    set t1 : T := Quotient.out q1
    set t2 : T := Quotient.out q2
    have hgT : g ∈ T := hΓT hg
    have hs : y * k * y⁻¹ = ((t1 : G))⁻¹ * g⁻¹ * (t2 : G) := by
      have ht2 : (t2 : G) = g * ((t1 : G) * y) * k * y⁻¹ := by rw [← he]; group
      rw [ht2]; group
    have hsT : y * k * y⁻¹ ∈ T := by
      rw [hs]; exact T.mul_mem (T.mul_mem (T.inv_mem t1.2) (T.inv_mem hgT)) t2.2
    have hsC : y * k * y⁻¹ ∈ C := by
      refine ⟨hsT, (memconj K y _).2 ?_⟩
      simpa [mul_assoc] using hk
    rw [DoubleCoset.eq]
    refine ⟨⟨g, hgT⟩, ?_, ⟨y * k * y⁻¹, hsT⟩, ?_, ?_⟩
    · simpa [A, Subgroup.mem_subgroupOf] using hg
    · simpa [B, Subgroup.mem_subgroupOf] using hsC
    · apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [hs]; group
  haveI : Finite {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0} := hsupp.to_subtype
  haveI hQ : Finite (DoubleCoset.Quotient (A : Set T) (B : Set T)) :=
    Finite.of_injective (fun q => (⟨φ q, hφS q⟩ : {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0}))
      (fun a b h => hφinj (congrArg Subtype.val h))

  have hpos : ∀ q : DoubleCoset.Quotient (A : Set T) (B : Set T),
      0 < ((Nat.card (A ⊓ B.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup T) : ℕ) : ℚ)⁻¹ := by
    intro q
    set t : T := Quotient.out q
    haveI : Finite ↥(Γ' ⊓ K.map (MulAut.conj ((t : G) * y)).toMonoidHom) := (hfin ((t : G) * y)).to_subtype
    have hmem : ∀ x : ↥(A ⊓ B.map (MulAut.conj t).toMonoidHom),
        ((x : T) : G) ∈ Γ' ⊓ K.map (MulAut.conj ((t : G) * y)).toMonoidHom := by
      intro x
      have hx := x.2
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxA, hxB⟩ := hx
      rw [memconjT] at hxB
      have hxC : ((t⁻¹ * (x : T) * t : T) : G) ∈ C := hxB
      refine ⟨hxA, (memconj K _ _).2 ?_⟩
      have := (memconj K y _).1 hxC.2
      simpa [mul_assoc] using this
    haveI : Finite ↥(A ⊓ B.map (MulAut.conj t).toMonoidHom) :=
      Finite.of_injective (fun x => (⟨((x : T) : G), hmem x⟩ : ↥(Γ' ⊓ K.map (MulAut.conj ((t : G) * y)).toMonoidHom)))
        (by intro a b h; apply Subtype.ext; apply Subtype.ext; have h' := congrArg Subtype.val h; exact h')
    exact inv_pos.mpr (Nat.cast_pos.mpr Nat.card_pos)
  haveI := Fintype.ofFinite (DoubleCoset.Quotient (A : Set T) (B : Set T))
  unfold massC
  rw [finsum_eq_sum_of_fintype]
  exact ne_of_gt (Finset.sum_pos (fun q _ => hpos q) Finset.univ_nonempty)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesNotPairwiseConjugate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult
open scoped Pointwise

namespace GlobalTheory.TypePlaces

theorem star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  letI := D.host.isCMField_hostE
  show D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem not_isConjPl : ∀ {D : D7} (Pb : Formalism.L2.Host.PiBar D.host) (Pg : Finset (Pl D.host.E)), (∀ PP, PP ∈ Pg ↔ ∃ k, Pb.Div k PP) → ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl PP PP' := by
  intro D Pb Pg hPg PP hP PP' hP' hc
  obtain ⟨k, hk⟩ := (hPg PP).1 hP
  obtain ⟨k', hk'⟩ := (hPg PP').1 hP'
  have hle : D.host.conj • PP.asIdeal ≤ PP'.asIdeal := by
    intro y hy
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
    obtain ⟨z, hzv, hz⟩ := hc _ hy
    have e : z = y := RingOfIntegers.ext
      ((hz.trans (star_eq_conj D _)).trans (D.host.conj.apply_symm_apply (y : D.host.E)))
    exact e ▸ hzv
  have hmax : (D.host.conj • PP.asIdeal).IsMaximal := by
    have := PP.isPrime
    refine Ideal.IsPrime.isMaximal inferInstance fun h0 => PP.ne_bot ?_
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using this
  have heq : D.host.conj • PP.asIdeal = PP'.asIdeal := hmax.eq_of_le PP'.isPrime.ne_top hle
  obtain ⟨ho, hm⟩ := (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) PP
    (Pb.overP hk)).2.2.2 (Pb.pb k) (Pb.pb_over k) PP' ((GlobalTheory.Mem.Chr.conjPl_iff_smul D.host.conj PP PP').2 heq)
  have hkk : k ≠ k' := by
    rintro rfl
    exact hm.1 hk hk'
  have ho' := Pb.overP hk'
  have hne : D.host.g k ≠ D.host.g k' := by
    have := D.host.g_ne
    fin_cases k <;> fin_cases k'
    · exact absurd rfl hkk
    · exact this
    · exact this.symm
    · exact absurd rfl hkk
  have hco : IsCoprime ((D.host.g k : ℕ) : 𝓞 D.host.E) ((D.host.g k' : ℕ) : 𝓞 D.host.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes (D.host.g_prime k) (D.host.g_prime k')).2 hne)
  obtain ⟨a, b, hab⟩ := hco
  apply PP'.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact add_mem (Ideal.mul_mem_left _ _ ho) (Ideal.mul_mem_left _ _ ho')

end GlobalTheory.TypePlaces
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryEquationBaseChangeAlgHom
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Pointwise

namespace GlobalTheory

theorem unitaryEq_baseChange {F E R K : Type} [Field F] [Field E] [Algebra F E] [CommRing R]
    [Algebra F R] [CommRing K] [Algebra F K] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (φ : R →ₐ[F] K) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :
    Formalism.UG.cT (sigR R σ) g * JR R J * g = JR R J →
    Formalism.UG.cT (sigR K σ) (g.map (Algebra.TensorProduct.map φ (AlgHom.id F E))) * JR K J *
      g.map (Algebra.TensorProduct.map φ (AlgHom.id F E)) = JR K J := by
  intro h
  set φ' : R ⊗[F] E →+* K ⊗[F] E := (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom
    with hφ'
  have hsig : ∀ x, φ' (sigR R σ x) = sigR K σ (φ' x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [hφ', sigR]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hJ : (JR R J).map φ' = JR K J := by
    ext i j
    simp [JR, inclR, hφ']
  have hcT : (Formalism.UG.cT (sigR R σ) g).map φ' = Formalism.UG.cT (sigR K σ) (g.map φ') := by
    ext i j
    simp [Formalism.UG.cT, hsig]
  have h2 := congrArg (fun A => A.map φ') h
  simp only [Matrix.map_mul] at h2
  rw [hcT, hJ] at h2
  exact h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIntegralAdelicElementExists
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameMove

open Formalism.UG (bc cT)

theorem conj_gram {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A)
    (β G h : GL (Fin n) A) (hG : G.val = cT σ β.val * J * β.val)
    (hx : β * h * β⁻¹ ∈ Formalism.UG.UJ σ J) :
    (G * h * G⁻¹).val = cT σ (h⁻¹).val := by
  have hx' : cT σ (β * h * β⁻¹).val * J * (β * h * β⁻¹).val = J := hx
  have e1 : cT σ h.val * G.val * h.val = G.val := by
    have e : (β * h * β⁻¹).val * β.val = β.val * h.val := by
      rw [← Units.val_mul, inv_mul_cancel_right, Units.val_mul]
    calc cT σ h.val * G.val * h.val = cT σ (β.val * h.val) * J * (β.val * h.val) := by
          rw [hG, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT σ β.val * (cT σ (β * h * β⁻¹).val * J * (β * h * β⁻¹).val) * β.val := by
          rw [← e, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = G.val := by rw [hx', hG]
  have e2 : cT σ (h⁻¹).val * cT σ h.val = 1 := by
    rw [← Formalism.UG.cT_mul, Units.mul_inv, Formalism.UG.cT_one]
  calc (G * h * G⁻¹).val = (cT σ (h⁻¹).val * cT σ h.val) * (G.val * h.val * (G⁻¹).val) := by
        rw [e2, Matrix.one_mul]; rfl
    _ = cT σ (h⁻¹).val * ((cT σ h.val * G.val * h.val) * (G⁻¹).val) := by simp only [Matrix.mul_assoc]
    _ = cT σ (h⁻¹).val := by rw [e1, Units.mul_inv, Matrix.mul_one]

theorem conj_gram_sub {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (O : Subring A) (J : Matrix (Fin n) (Fin n) A)
    (β : GL (Fin n) A) (G h : GL (Fin n) O) (hG : (bc O.subtype G).val = cT σ β.val * J * β.val)
    (hx : β * bc O.subtype h * β⁻¹ ∈ Formalism.UG.UJ σ J) (i j : Fin n) :
    (((G * h * G⁻¹).val i j : O) : A) = σ ((h⁻¹).val j i : O) := by
  have c := conj_gram σ J β (bc O.subtype G) (bc O.subtype h) hG hx
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul] at c
  exact congrFun (congrFun c i) j

end GlobalTheory.FrameMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassModelUnitDiscriminantAwayFromP
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem sqrtNegNat_im_ne_zero {p : ℕ} (hp : 0 < p) : (sqrtNegNat p).im ≠ 0 := by
  have : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.2 (by exact_mod_cast hp)
  simpa [sqrtNegNat] using this.ne'

theorem modelAt_one_of_sqProd_mem : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ),
    p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → sqProd p L t ∈ F →
    ∀ V : ValuationSubring ℂ, V.valuation (p : ℂ) = 1 → ModelAt V F (latticeCurve L) 1 := by
  intro p F L t hp hp4 hp3 hD hQ V hVp
  have hβ : (sqrtNegNat p).im ≠ 0 := sqrtNegNat_im_ne_zero hp.pos
  have hΔF : (latticeCurve L).Δ ∈ F := by
    rw [latticeCurve_Δ]
    exact sub_mem (pow_mem hD.g₂_mem 3) (mul_mem (by simpa using (algebraMap_mem F (27 : ℚ))) (pow_mem hD.g₃_mem 2))
  obtain ⟨A, hAF, hA0, hAv⟩ := GlobalTheory.T.exists_cube_valuation_eq_discriminant p F L t hp hp4 hp3 hD V
  obtain ⟨u, huF, hu0, huv⟩ := _root_.GlobalTheory.valuation_twelfth_power_of_cube p V F (latticeCurve L).Δ A (sqProd p L t) hp4 hΔF hAF hQ
    (latticeCurve_Δ_ne_zero L) hA0 hAv (GlobalTheory.T.prodDerivWeierstrassPOverSquares_pow_eight_mul p F L t hp hp4 hp3 hD)
  rw [hVp, one_pow, mul_one] at huv
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  by_cases h2 : V.valuation (2 : ℂ) = 1
  · by_cases h3 : V.valuation (3 : ℂ) = 1
    ·
      have h6 : V.valuation (6 : ℂ) = 1 := by
        rw [show (6 : ℂ) = 2 * 3 by norm_num, map_mul, h2, h3, one_mul]
      have hj : (latticeCurve L).j ∈ V :=
        ReciprocityTheory.Gal.mem_of_isIntegral_int V (_root_.GlobalTheory.CMModel.LatticeJInt.main L (sqrtNegNat p) hD.mul hβ)
      exact _root_.GlobalTheory.CMModel.modelAt_short_of_six_unit V F (-L.g₂ / 4) (-L.g₃ / 4) (latticeCurve L).j u 1 hj
        (GlobalTheory.j_mul_Δ (latticeCurve L)) h6 huF hu0 (one_mem V) (by rw [map_one, mul_one]; exact huv)
    ·
      obtain ⟨N, ι, hι, T, hNodd, hN3, hNv, hcard, hT, hTor⟩ := _root_.GlobalTheory.CMModel.exists_stable_family_ker p F L t hp hp4 hp3 hD V
      have hcop : Nat.Coprime (Fintype.card ι) 3 := by
        rw [hcard]
        exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega))
      have hc : V.valuation (Fintype.card ι : ℂ) = 1 := by
        rcases GlobalTheory.T.valuation_natCast_eq_one_or_of_coprime V _ _ hcop with h | h
        · exact h
        · exact absurd (by simpa using h) h3
      exact _root_.GlobalTheory.CMModel.modelAt_of_stable_torsion L (sqrtNegNat p) u V N hD.mul hβ huv hNv hNodd F ι T hD.g₂_mem hD.g₃_mem huF
        hT hTor hc
  ·
    obtain ⟨-, hodd'⟩ := _root_.GlobalTheory.CMModel.card_sq_mod_prime p hp hp4
    have hcop : Nat.Coprime (Fintype.card (Sq p)) 2 :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by rcases hodd' with ⟨k, hk⟩; omega))
    have hc : V.valuation (Fintype.card (Sq p) : ℂ) = 1 := by
      rcases GlobalTheory.T.valuation_natCast_eq_one_or_of_coprime V _ _ hcop with h | h
      · exact h
      · exact absurd (by simpa using h) h2
    exact _root_.GlobalTheory.CMModel.modelAt_of_stable_torsion L (sqrtNegNat p) u V p hD.mul hβ huv hVp hodd F (Sq p) (sqPt p t)
      hD.g₂_mem hD.g₃_mem huF ((_root_.GlobalTheory.CMModel.sqProd_sq_mem_and_stable p F L t hp hp4 hp3 hD).2 hQ)
      (_root_.GlobalTheory.CMModel.SqNe.sqPt_and_sqProd_ne_zero p F L t hp hp4 hp3 hD).1 hc

end GlobalTheory.CMModel
end

