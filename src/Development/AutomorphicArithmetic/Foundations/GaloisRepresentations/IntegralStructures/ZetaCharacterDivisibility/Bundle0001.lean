module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0680
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.CocharacterLieDivisors.CocharacterLieAlgebra.PCocharToLie
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0211

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.CharOfZeta
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Int.Div

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

abbrev cj : Ideles E →* Ideles E := Units.map (conjAd E).toMonoidHom

def quo : Ideles E →* Ideles E := (MonoidHom.id (Ideles E)) / cj E

theorem quo_apply (z : Ideles E) : quo E z = z / cj E z := rfl

def IsZeta (a : ℕ) (ζ : Ideles E →* UA E a) : Prop :=
  ∀ z, ((ζ z : UA E a) : GA E a) = Matrix.GeneralLinearGroup.scalar (Fin a) (quo E z)

def ZetaEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), ∃ ζ : Ideles E →* UA E a, IsZeta E a ζ ∧ Continuous ζ ∧
    (∀ z x, ζ z * x = x * ζ z) ∧ (∀ k : Eˣ, ζ (diagUnits E k) ∈ ratU E a) ∧ ∀ z, cj E z = z → ζ z = 1

def ZetaLoc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (ζ : Ideles E →* UA E a), IsZeta E a ζ →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ u : (w.adicCompletion E)ˣ,
      ζ (localIdele E w u) ∈ locU a w ∧ cLoc w (ζ (localIdele E w u)) = Matrix.GeneralLinearGroup.scalar (Fin a) u

def SchurU : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U →
    ∀ z : UA E a, (∀ x, z * x = x * z) → ∃ c : ℂ, ∀ φ ∈ U, RU E a z φ = c • φ

def CharOfZeta : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U →
    ∀ ζ : Ideles E →* UA E a, Continuous ζ → (∀ z x, ζ z * x = x * ζ z) → (∀ k : Eˣ, ζ (diagUnits E k) ∈ ratU E a) →
    (∀ z, ∃ c : ℂ, ∀ φ ∈ U, RU E a (ζ z) φ = c • φ) →
    ∃ χ : HChar E, ∀ z, ∀ φ ∈ U, RU E a (ζ z) φ = ((χ.1 z : ℂˣ) : ℂ) • φ

def AlgOfFix : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar E), (∀ z, cj E z = z → χ.1 z = 1) →
    ∃ n : (E →+* ℂ) → ℤ, IsAlgPos χ n

def SatCent : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B → ∃ x : σ.V, x ≠ 0 ∧
      (∀ u : (w.adicCompletion E)ˣ, IsUnitAt w u → σ.ρ (Matrix.GeneralLinearGroup.scalar (Fin a) u) x = x) ∧
      ∀ u : (w.adicCompletion E)ˣ, IsUnifAt w u →
        σ.ρ (Matrix.GeneralLinearGroup.scalar (Fin a) u) x = ((B.prod : ℂˣ) : ℂ) • x

end UpperTheory.Gal.Int.Div

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.HtCocharOf
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

namespace UpperTheory.Gal.Int.Div

theorem htCochar_of (hJ : JumpCard) : PositivityTheory.AutomorphicGaloisHodgeTate.Div.HTCochar := by
  intro E Ω _ _ _ _ _ l _ N n V _ ⟨P, AI, hT, w, A, _, _, O, i1, i2, i3, Bw, _, τ, J, hj, ks, k1, k2, k3⟩
  have hc : J.card = N := by
    obtain ⟨L, r', hm, hd, τ', ht, hcnt⟩ := id hj
    obtain ⟨J', h1, h2⟩ := hJ l P AI hT E Ω A O Bw N _ ⟨L, r', hm, hd⟩ τ L τ' ht
    rw [← h2]
    congr 1
    ext a
    exact_mod_cast (hcnt a).trans (h1.count_eq P hm ht a).symm
  obtain ⟨T⟩ := hT
  obtain ⟨Pm, k, hk, hf⟩ := GlobalTheory.HodgeTateCochar.mem_closure_of_jumps l P AI T Bw _ τ J hj hc
  refine ⟨ℂ_[l], inferInstance, inferInstance, inferInstance, Pm.val, k, ks, (Matrix.isUnit_iff_isUnit_det _).1 Pm.isUnit, k1, k3,
    fun i => ?_, fun f h0 t ht => ?_⟩
  · have := k2 i
    rw [← hk] at this
    obtain ⟨j, -, e⟩ := Multiset.mem_map.1 this
    exact ⟨j, e⟩
  · rw [← Matrix.coe_units_inv]
    refine hf Bw.Kw le_rfl _ (fun g _ => ?_) t ht
    have := congrArg (algebraMap (Qbar l) ℂ_[l]) (h0 g)
    rw [map_zero, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left] at this
    rw [MvPolynomial.eval_map]
    exact this

theorem senWLac_of (hJ : JumpCard) : SenWLac := PositivityTheory.AutomorphicGaloisHodgeTate.Div.cocharToLie_holds (htCochar_of hJ)

end UpperTheory.Gal.Int.Div
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PCoverIn
section
namespace UpperTheory.Gal.Int.Div

open GlobalTheory.BlockSum (blockRep)

theorem coverIn_of : CoverIn := by
  intro Γ k _ _ a d r ρ ⟨m, B, hB, hg⟩
  let n := Fintype.card (Σ _ : Fin m, Fin a)
  let e : (Σ _ : Fin m, Fin a) ≃ Fin n := Fintype.equivFin _
  let σ : Fin n ≃ Fin a × Fin m := e.symm.trans ((Equiv.sigmaEquivProd _ _).trans (Equiv.prodComm _ _))
  refine ⟨m, n, e, B.submatrix σ id, ?_, fun g => ?_⟩
  · have h := Matrix.rank_submatrix B σ (Equiv.refl _)
    simpa [hB] using h
  · have key : ((blockRep (a := fun _ : Fin m => a) e fun _ => r) g : Matrix (Fin n) (Fin n) k) =
        (Matrix.kronecker (r g : Matrix (Fin a) (Fin a) k) (1 : Matrix (Fin m) (Fin m) k)).submatrix σ σ := by
      rw [GlobalTheory.BlockSum.blockRep_val]
      ext i j
      obtain ⟨⟨x, u⟩, rfl⟩ := e.surjective i
      obtain ⟨⟨y, v⟩, rfl⟩ := e.surjective j
      simp [σ, Matrix.blockDiagonal'_apply, Matrix.one_apply, Matrix.kroneckerMap_apply]
    rw [key]
    have h1 : B.submatrix σ id = B.submatrix σ (Equiv.refl _) := rfl
    have h2 : (ρ g : Matrix (Fin d) (Fin d) k) = (ρ g : Matrix (Fin d) (Fin d) k).submatrix (Equiv.refl _) (Equiv.refl _) := by simp
    rw [h1, Matrix.submatrix_mul_equiv, hg g, h2, Matrix.submatrix_mul_equiv]
    simp

end UpperTheory.Gal.Int.Div
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PDGenMul
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.dGenMul_of :
    DGenMul := by
  classical
  intro a q B ha hc hG
  obtain ⟨α, rfl⟩ : ∃ α : Fin a → ℂˣ, Finset.univ.val.map α = B := by
    induction B using Quotient.inductionOn with
    | h l =>
      have hl : l.length = a := hc
      subst hl
      exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩
  refine UpperTheory.Gal.crystallineComparison.genMul_of ℂˣ a α ?_
  intro m hs hp
  have hne := hG α rfl
  unfold DGen at hne
  rw [map_mul] at hne
  have h3 := right_ne_zero_of_mul hne
  rw [map_prod] at h3
  have hle : ∀ i, m i < a + 1 := fun i => Nat.lt_succ_of_le
    (hs ▸ Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  have hone : ((1 : Fin (a + 1)) : ℕ) = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  by_cases hm : (fun i => (⟨m i, hle i⟩ : Fin (a + 1))) = fun _ => 1
  · intro i
    have h := congrArg Fin.val (congrFun hm i)
    rw [hone] at h
    exact h
  · exfalso
    have hmem : (fun i => (⟨m i, hle i⟩ : Fin (a + 1))) ∈
        (Finset.univ : Finset (Fin a → Fin (a + 1))).filter
          (fun m => (∑ i, (m i : ℕ)) = a ∧ m ≠ fun _ => 1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs, hm⟩
    refine Finset.prod_ne_zero_iff.mp h3 _ hmem ?_
    have hp' : ∏ i, (α i : ℂ) ^ m i = ∏ i, (α i : ℂ) := by
      have h := congrArg Units.val hp
      simpa [Units.coe_prod] using h
    simpa [map_sub, map_prod, map_pow, MvPolynomial.aeval_X] using sub_eq_zero.mpr hp'
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PDivDet
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.divDet_of :
    DenseUs → DetFrob → DivDet := by
  intro hD hF E Ω _ _ _ _ _ _ l _ ι a d hd U hU ψ hψ r hr g
  obtain ⟨hrc, -, V, X, hVo, hVd, hV⟩ := hr
  have hc1 : Continuous fun g : G E Ω => (r g : Matrix (Fin a) (Fin a) (Qbar l)).det :=
    Continuous.matrix_det (Units.continuous_val.comp hrc)
  have hc2 : Continuous fun g : G E Ω => ((ψ g : (Qbar l)ˣ) : Qbar l) :=
    Units.continuous_val.comp hψ.1
  have hdense := ((hD E Ω l a d hd U hU X).inter_of_isOpen_right hVd hVo).preimage
    (Homeomorph.inv (G E Ω)).isOpenMap
  refine congrFun (Continuous.ext_on hdense hc1 hc2 ?_) g
  rintro x ⟨⟨w, hwX, hUs, hl, ⟨B, hB⟩, A, hA, hFr⟩, hxV⟩
  have hx : (x⁻¹)⁻¹ = x := inv_inv x
  have hch := (hV w hwX hUs hl B hB A hA).2 x⁻¹ hFr hxV
  rw [hx] at hch
  have hψv := (hF E Ω l ι a U ψ hψ w hUs.1 hl B hB A hA).2 x⁻¹ hFr
  rw [hx] at hψv
  apply ι.injective
  rw [hψv]
  have hcard : (algSat a (normV w) B).card = a := by
    have h1 := congrArg Polynomial.natDegree hch
    rw [Polynomial.natDegree_map, Matrix.charpoly_natDegree_eq_dim,
      Polynomial.natDegree_multiset_prod_X_sub_C_eq_card] at h1
    simpa using h1.symm
  have h0 := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p 0) hch
  simp only [Polynomial.coeff_map] at h0
  have hdet : (r x : Matrix (Fin a) (Fin a) (Qbar l)).det =
      (-1) ^ a * (r x : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.coeff 0 := by
    simpa using Matrix.det_eq_sign_charpoly_coeff (r x : Matrix (Fin a) (Fin a) (Qbar l))
  have h1 : ι ((r x : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.coeff 0) =
      (Multiset.map (fun b => Polynomial.X - C b) (algSat a (normV w) B)).prod.coeff 0 := h0
  have h2 : (Multiset.map (fun b => Polynomial.X - C b) (algSat a (normV w) B)).prod.coeff 0 =
      (-1) ^ a * (algSat a (normV w) B).prod := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_multiset_prod, Multiset.map_map]
    have : (Multiset.map (Polynomial.eval 0 ∘ fun b : ℂ => Polynomial.X - C b) (algSat a (normV w) B)) =
        Multiset.map Neg.neg (algSat a (normV w) B) :=
      Multiset.map_congr rfl fun b _ => by simp
    rw [this, Multiset.prod_map_neg, hcard]
  show ι (r x : Matrix (Fin a) (Fin a) (Qbar l)).det = _
  rw [hdet, map_mul, h1, h2, map_pow, map_neg, map_one, ← mul_assoc, ← mul_pow]
  simp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PDivOne
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

private theorem satPol_facts {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (s : Multiset ℂ) :
    (((s.map fun b => X - C b).prod).map ι.symm.toRingHom).Monic ∧
    (((s.map fun b => X - C b).prod).map ι.symm.toRingHom).natDegree = Multiset.card s ∧
    (((s.map fun b => X - C b).prod).map ι.symm.toRingHom).coeff 0 = ι.symm ((-1) ^ Multiset.card s * s.prod) ∧
    (((s.map fun b => X - C b).prod).map ι.symm.toRingHom).map ι.toRingHom = (s.map fun b => X - C b).prod := by
  refine ⟨(monic_multiset_prod_of_monic _ _ fun b _ => monic_X_sub_C b).map _, ?_, ?_, ?_⟩
  · rw [natDegree_map, natDegree_multiset_prod_X_sub_C_eq_card]
  · rw [coeff_map, coeff_zero_eq_eval_zero, eval_multiset_prod, Multiset.map_map]
    have : (s.map ((fun p : ℂ[X] => eval 0 p) ∘ fun b => X - C b)) = s.map Neg.neg := by
      refine Multiset.map_congr rfl fun b _ => ?_
      simp
    rw [this, Multiset.prod_map_neg]
    rfl
  · rw [Polynomial.map_map]
    have : ι.toRingHom.comp ι.symm.toRingHom = RingHom.id ℂ := by
      ext z
      simp
    rw [this, Polynomial.map_id]

theorem UpperTheory.Gal.Int.Div.divOne_of :
    DivSet → DenseUs → DetFrob → InFacts → SepPin → DivOne := by
  intro hDiv hDense hDet hIn hSep E Ω _ _ _ _ _ _ l _ ι a d hd U hU ψ hψ dd ρ hV
  obtain ⟨hc, hs, ⟨X, hX⟩, hr⟩ := hV
  have hcard : ∀ (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), SatU U w B →
      Multiset.card (algSat a (normV w) B) = a := by
    rintro w B ⟨σ, -, hB⟩
    have h : Multiset.card (algSat a (normV w) B) = Multiset.card B := by
      unfold algSat
      simp
    rw [h]
    exact GlobalTheory.LFun.HasSatGL.card hB
  have hD := (hDense E Ω l a d hd U hU X).preimage (Homeomorph.inv (G E Ω)).isOpenMap
  obtain ⟨r, hrc, hrs, hin, hco, hop, hde⟩ := hDiv E Ω l a dd ρ hc hs hr ψ hψ.1 (hD.mono (by
    rintro g ⟨w, hw, hu, hl, ⟨B, hB⟩, A, hA, hf⟩
    have hf' : IsFrob A (normV w) g⁻¹ := hf
    obtain ⟨q1, q2, q3, -⟩ := satPol_facts ι (algSat a (normV w) B)
    rw [hcard w B hB] at q2 q3
    refine ⟨_, q1, q2, ?_, ?_⟩
    · have := (hX w hw hu hl B hB A hA).2 g⁻¹ hf'
      rwa [inv_inv] at this
    · have h := (hDet E Ω l ι a U ψ hψ w hu.1 hl B hB A hA).2 g⁻¹ hf'
      rw [inv_inv] at h
      rw [q3]
      apply ι.injective
      have h1 : ((-1 : ℂ) ^ a) * (-1) ^ a = 1 := by
        rw [← mul_pow]; simp
      simp only [map_mul, map_pow, map_neg, map_one, RingEquiv.apply_symm_apply]
      rw [h, ← mul_assoc, h1, one_mul]))
  refine ⟨r, ⟨hrc, hrs, (fun g : G E Ω => g⁻¹) ⁻¹' {g | (r g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.Separable}, X,
    hop.preimage continuous_inv, hde.preimage (Homeomorph.inv (G E Ω)).isOpenMap, ?_⟩, hin, hco⟩
  intro w hw hu hl B hB A hA
  have hE := hX w hw hu hl B hB A hA
  have hF := hIn (G E Ω) (Qbar l) a dd r ρ hin
  refine ⟨fun s hs' => hF.2.1 s (hE.1 s hs'), fun s hf hsV => ?_⟩
  obtain ⟨q1, q2, -, q4⟩ := satPol_facts ι (algSat a (normV w) B)
  rw [hcard w B hB] at q2
  rw [hSep (Qbar l) a _ _ q1 q2 (hF.2.2 s⁻¹ _ (hE.2 s hf)) hsV, q4]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PDivSet
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.divSet_of :
    DivWCoreLac → SenWLac → LacBridge → InFacts → DivSet := by
  intro hcore hsen hlac _ E Ω _ _ _ _ _ l _ a dd ρ hρ hss hHT ψ hψ hD
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : IsGalois E Ω := {}
  have : CompactSpace (G E Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[E] Ω))
  obtain ⟨K', _, _, _, X, hX, hroots⟩ := hsen E Ω l dd a ρ hρ (hlac E Ω l a dd ρ hHT)
  let T : G E Ω → (Qbar l)[X] → Prop := fun g Q => Q.Monic ∧ Q.natDegree = a ∧
    aeval (ρ g : Matrix (Fin dd) (Fin dd) (Qbar l)) Q = 0 ∧
      ((ψ g : (Qbar l)ˣ) : Qbar l) = (-1) ^ a * Q.coeff 0
  let P : G E Ω → (Qbar l)[X] := fun g => if h : ∃ Q, T g Q then h.choose else 1
  have hP : ∀ s ∈ {g : G E Ω | ∃ Q, T g Q}, T s (P s) := by
    intro s hs
    have e : P s = (show ∃ Q, T s Q from hs).choose := dif_pos hs
    rw [e]
    exact (show ∃ Q, T s Q from hs).choose_spec
  have hss' : IsSSMat ρ := by
    intro W hW
    obtain ⟨W', h1, h2⟩ := hss W hW
    exact ⟨W', h2, h1⟩
  obtain ⟨r, hrc, hrss, hin, hco, -, -, -, hopen, hdense, -, -⟩ :=
    hcore (G E Ω) (Qbar l) K' dd a ρ (Units.continuous_val.comp hρ) hss'
      {g : G E Ω | ∃ Q, T g Q} hD P
      (fun s hs => ⟨(hP s hs).1, (hP s hs).2.1⟩) (fun s hs => (hP s hs).2.2.1)
      X hX hroots ψ (Units.continuous_val.comp hψ) (fun s hs => (hP s hs).2.2.2)
  refine ⟨r, ?_, ?_, hin, hco, hopen, hdense⟩
  · refine Units.continuous_iff.mpr ⟨hrc, ?_⟩
    simp only [← map_inv]
    exact hrc.comp continuous_inv
  · intro W hW
    obtain ⟨W', h1, h2⟩ := hrss W hW
    exact ⟨W', h2, h1⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PGenPin
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

private theorem aeval_matrix_map {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (Q : K[X]) :
    aeval (M.map f) (Q.map f) = (aeval M Q).map f := by
  simp only [aeval_def, eval₂_map]
  have h := hom_eval₂ Q (algebraMap K (Matrix (Fin n) (Fin n) K)) f.mapMatrix M
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at h
  rw [h]
  congr 1
  ext a : 1
  simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_map]

theorem UpperTheory.Gal.Int.Div.genPin_of :
    GenPin := by
  intro l _ ι a M s hcard hgen hann hdet
  set P := (Multiset.map (fun b ↦ X - C b) s).prod with hPdef
  have hround : map ι.toRingHom (map ι.symm.toRingHom P) = P := by
    rw [Polynomial.map_map]
    convert Polynomial.map_id
    ext z
    simp
  have hann2 : aeval (M.map ι.toRingHom) (UpperTheory.Gal.crystallineComparison.rootPol s) = 0 := by
    show aeval (M.map ι.toRingHom) P = 0
    rw [← hround, aeval_matrix_map, hann]
    simp
  have hdet2 : (M.map ι.toRingHom).det = s.prod := by
    have hd := RingHom.map_det ι.toRingHom M
    rw [RingHom.mapMatrix_apply] at hd
    rw [← hd]
    exact hdet
  rw [← Matrix.charpoly_map]
  exact UpperTheory.Gal.crystallineComparison.charAnn_of ℂ a _ s hcard hgen hann2 hdet2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PJumpCard
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.jumpCard_of :
    JumpCard := by
  intro l _ P AI tied E Ω _ _ _ _ _ A O _ _ _ Bw a r hdR τ LL' τ' hτ
  obtain ⟨T⟩ := id tied
  obtain ⟨L₀, r₀, hm, hd⟩ := hdR
  have l₁ : L₀.1 ≤ (supExt L₀ LL').1 := le_sup_left
  have l₂ : LL'.1 ≤ (supExt L₀ LL').1 := le_sup_right
  have hm' := hm.enlarge l₁
  have hd' := (local_ext P Bw l₁ r₀).2.1.2 hd
  have hτ' : IsInduced Bw τ ((IntermediateField.inclusion l₂).comp τ') := fun x => hτ x
  have hdr' : IsDR (P.PD Bw.Kw) (Bw.repE (supExt L₀ LL') (mapRep (IntermediateField.inclusion l₁).toRingHom r₀)) := by
    rw [IsDR, Module.finrank_fin_fun]
    exact hd'
  obtain ⟨hfin, -, hrk⟩ := (GlobalTheory.Per.Components.components_finrank l P AI T _ (supExt L₀ LL') _
    (Bw.repE (supExt L₀ LL') (mapRep (IntermediateField.inclusion l₁).toRingHom r₀))).1
      ((IntermediateField.inclusion l₂).comp τ')
  obtain ⟨J', h1, h2⟩ := @GlobalTheory.HtCardProof.exists_count _ _ _ _ _ T _ _
    ((mapRep (IntermediateField.inclusion l₁).toRingHom r₀).comp Bw.e.symm.toMonoidHom)
    ((IntermediateField.inclusion l₂).comp τ') hfin
  exact ⟨J', ⟨_, _, hm', hd', _, hτ', h2⟩, h1.trans ((hrk hdr').trans (Module.finrank_fin_fun _))⟩
end

