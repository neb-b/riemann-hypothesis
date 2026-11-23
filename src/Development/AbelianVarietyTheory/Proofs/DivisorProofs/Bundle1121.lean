module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1033
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianModelOfNormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitLength
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1018
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0704
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0998
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1073

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeLinearFactorsRegroup
section
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.multiset_map_prod_finset_sum {α β γ : Type} [CommMonoid γ] (F : α → γ) (s : Finset β)
    (m : β → Multiset α) :
    ((∑ i ∈ s, m i).map F).prod = ∏ i ∈ s, ((m i).map F).prod := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Multiset.map_add (f := _), Multiset.prod_add, ih]

theorem GlobalTheory.satake_linear_factors_regroup : ∀ (K : Type) [Field K] (ι : K ≃+* ℂ) (c : ℕ) (d : Fin c → ℕ) (S : Fin c → Multiset ℂˣ) (T : Multiset ℂˣ) (q : ℕ),
  q ≠ 0 → ∀ e : ℂ,
  ∑ i, ∑ k : Fin (d i), (S i).map (fun z => (z : ℂ) * (q : ℂ) ^ (((d i : ℂ) - 1) / 2 - (k : ℕ))) = T.map (fun z => (z : ℂ)) →
  (T.map fun z : ℂˣ => Polynomial.X - Polynomial.C (ι.symm ((z : ℂ) * (q : ℂ) ^ e))).prod =
    ∏ i, ∏ k : Fin (d i), ((S i).map fun z : ℂˣ =>
      Polynomial.X - Polynomial.C (ι.symm ((z : ℂ) * (q : ℂ) ^ (e + (((d i : ℂ) - 1) / 2 - (k : ℕ)))))).prod := by
  intro K _ ι c d S T q hq e hT
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  set F : ℂ → Polynomial K := fun u => Polynomial.X - Polynomial.C (ι.symm (u * (q : ℂ) ^ e)) with hF
  have h1 : (T.map fun z : ℂˣ => Polynomial.X - Polynomial.C (ι.symm ((z : ℂ) * (q : ℂ) ^ e))) =
      (T.map (fun z : ℂˣ => (z : ℂ))).map F := by
    rw [Multiset.map_map]; rfl
  have hc : ∀ M : Multiset ℂˣ, (do let a ← M; pure (a : ℂ) : Multiset ℂ) = M.map (fun z : ℂˣ => (z : ℂ)) :=
    fun M => Multiset.bind_singleton M _
  simp only [hc, Multiset.map_id'] at hT
  rw [h1, ← hT, GlobalTheory.multiset_map_prod_finset_sum]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [GlobalTheory.multiset_map_prod_finset_sum]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [Multiset.map_map, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl (fun z _ => ?_)
  simp only [Function.comp, hF]
  rw [Complex.cpow_add _ _ hq']
  ring_nf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.Hk3

theorem schurAll_of_cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), SchurAll R :=
  fun hP _ _ _ _ _ _ _ _ _ _ _ _ =>
    ⟨fun _ _ _ => GlobalTheory.MultFinite.schurMult hP _ _, GlobalTheory.MultFinite.schurMult hP _ _,
      fun _ => GlobalTheory.MultFinite.schurMult hP _ _⟩

end GlobalTheory.Hk3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeStandardHermitian
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

noncomputable section

namespace GlobalTheory.InertUnitOrb.LatOnto

open GlobalTheory.InertUnitOrb.ModelOfN

theorem exists_orthonormal_mem {K : UQ} (n : ℕ) : ∀ (V : Type) [AddCommGroup V] [Module K.E V] [Module K.O V]
    [IsScalarTower K.O K.E V] [FiniteDimensional K.E V] (h : V → V → K.E),
    (∀ y y' z, h (y + y') z = h y z + h y' z) → (∀ (a : K.E) y z, h (a • y) z = a * h y z) →
    (∀ y z, h z y = K.c (h y z)) → Module.finrank K.E V = n → ∀ L : Submodule K.O V, L.FG →
    Submodule.span K.E (L : Set V) = ⊤ → (∀ y, y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap K.O K.E).range) →
    ∃ v : Fin n → V, (∀ i, v i ∈ L) ∧ ∀ i j, h (v i) (v j) = if i = j then 1 else 0 := by
  first
  | exact @_root_.GlobalTheory.InvolutionTraceUnit.exists_orthonormal
  | exact _root_.GlobalTheory.InvolutionTraceUnit.exists_orthonormal
  | (apply _root_.GlobalTheory.InvolutionTraceUnit.exists_orthonormal <;> assumption)
  | (intros; apply _root_.GlobalTheory.InvolutionTraceUnit.exists_orthonormal <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InvolutionTraceUnit.exists_orthonormal <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InvolutionTraceUnit.exists_orthonormal ..)

end GlobalTheory.InertUnitOrb.LatOnto

namespace GlobalTheory.InertUnitOrb.LatOnto

open GlobalTheory.InertUnitOrb.ModelOfN

theorem exists_unitLat_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ), B.σ (x : B.A) = x → (∀ y z, stdH K n (ψ y) (ψ z) = B.herm x y z) → ∀ L : Submodule K.O B.A, IsLat K.O K.E L → (∀ y, y ∈ L ↔ ∀ z ∈ L, B.herm x y z ∈ (algebraMap K.O K.E).range) → ∃ q : UL n w, unitLat e B ψ q = L := by
  intro E _ _ _ _ w hns K e he hint n B ψ x hσx hH L hLat hdual
  have hadd : ∀ y y' z, B.herm x (y + y') z = B.herm x y z + B.herm x y' z := by
    intro y y' z
    simp only [InvAlg.herm, mul_add, add_mul, map_add (f := _)]
  have hsmul : ∀ (a : K.E) y z, B.herm x (a • y) z = a * B.herm x y z := by
    intro a y z
    simp only [InvAlg.herm, mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul]
  have hsym : ∀ y z, B.herm x z y = K.c (B.herm x y z) := by
    intro y z
    simp only [InvAlg.herm]
    rw [← trace_sigma B, map_mul B.σ, map_mul B.σ, B.σ_σ, hσx]
    congr 1
    ring
  have hn : Module.finrank K.E B.A = n := by rw [ψ.finrank_eq, Module.finrank_fin_fun]
  obtain ⟨v, hvL, hv⟩ := exists_orthonormal_mem n B.A (B.herm x) hadd hsmul hsym hn L hLat.1 hLat.2 hdual
  obtain ⟨b, hb⟩ := exists_basis_of_orthonormal (B.herm x) hadd hsmul hn v hv
  let P : Matrix (Fin n) (Fin n) K.E := Matrix.of fun i j => ψ (v j) i
  let Pc : Matrix (Fin n) (Fin n) K.E := Formalism.UG.cT (K.c : K.E →+* K.E) P
  have hPc : ∀ i k, Pc i k = K.c (ψ (v i) k) := fun i k => rfl
  have hPP : Pc * P = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have h1 := hH (v j) (v i)
    simp only [stdH] at h1
    simp only [hPc, P, Matrix.of_apply]
    rw [show (∑ k, K.c (ψ (v i) k) * ψ (v j) k) = ∑ k, ψ (v j) k * K.c (ψ (v i) k) from
      Finset.sum_congr rfl fun k _ => mul_comm _ _, h1, hv]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  have hPP' : P * Pc = 1 := mul_eq_one_comm.1 hPP
  let eh : K.E →+* w.adicCompletion E := e.toRingHom
  have hmul1 : P.map eh * Pc.map eh = 1 := by
    rw [← Matrix.map_mul, hPP', Matrix.map_one _ (map_zero eh) (map_one eh)]
  have hmul2 : Pc.map eh * P.map eh = 1 := by
    rw [← Matrix.map_mul, hPP, Matrix.map_one _ (map_zero eh) (map_one eh)]
  let qG : GLw n w := ⟨P.map eh, Pc.map eh, hmul1, hmul2⟩
  have hcT : Formalism.UG.cT (cj w) (P.map eh) = Pc.map eh := by
    refine Matrix.ext fun i j => ?_
    change cj w (e (ψ (v i) j)) = e (K.c (ψ (v i) j))
    exact (he _).symm
  have hqU : qG ∈ UL n w := by
    unfold UL
    rw [if_neg hns]
    show Formalism.UG.cT (cj w) (P.map eh) * 1 * P.map eh = 1
    rw [hcT, Matrix.mul_one, hmul2]
  refine ⟨⟨qG, hqU⟩, ?_⟩
  have hinv : ((((⟨qG, hqU⟩ : UL n w)⁻¹ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map
      e.symm = Pc := by
    refine Matrix.ext fun i j => ?_
    show e.symm (e (Pc i j)) = Pc i j
    exact e.symm_apply_apply _
  have hcoef : ∀ y i, (Pc *ᵥ ψ y) i = B.herm x y (v i) := by
    intro y i
    rw [← hH]
    simp only [Matrix.mulVec, dotProduct, hPc, stdH]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hexp : ∀ y j, B.herm x y (v j) = b.repr y j := by
    intro y j
    conv_lhs => rw [← b.sum_repr y]
    rw [show B.herm x (∑ i, b.repr y i • b i) (v j) = ∑ i, b.repr y i * B.herm x (b i) (v j) from ?_]
    · simp only [hb, hv, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty]
        have := hsmul 0 0 (v j)
        simpa using this
      | insert a s ha ih' =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, hsmul, ih']
  unfold unitLat
  rw [hinv]
  ext y
  show (∀ i, (Matrix.toLin' Pc (ψ y)) i ∈ (algebraMap K.O K.E).range) ↔ y ∈ L
  simp only [Matrix.toLin'_apply, hcoef]
  constructor
  · intro H
    choose a ha using H
    have hy : y = ∑ i, a i • v i := by
      conv_lhs => rw [← b.sum_repr y]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hexp, ← ha, algebraMap_smul, hb]
    rw [hy]
    exact Submodule.sum_mem _ fun i _ => L.smul_mem _ (hvL i)
  · intro hy i
    exact (hdual y).1 hy (v i) (hvL i)

end GlobalTheory.InertUnitOrb.LatOnto
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparableCharpolyOfTestFunctionNeZeroRegularPlac
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.RegVan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mem_GLint_of_entries {L : Type} [Field L] {k : ℕ} (O : Subring L) (g : GL (Fin k) L)
    (h1 : ∀ i j, g.1 i j ∈ O) (h2 : ∀ i j, g⁻¹.1 i j ∈ O) : g ∈ Formalism.UG.GLint (Fin k) O := by
  have hi : Function.Injective fun A : Matrix (Fin k) (Fin k) O => A.map O.subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

theorem eventually_toSub_mem (x : finU (E := E) (n := n)) :
    ∀ᶠ w in cofinite, toSub (UL n w) (cLoc w (x : UA E n)) ∈ KL n w := by
  have h : ∀ y : FiniteAdeleRing (𝓞 E) E, ∀ᶠ w in cofinite, pLoc E w y ∈ Formalism.UG.Ov E w := fun y => y.2
  have h1 : ∀ᶠ w in cofinite, ∀ i j, pLoc E w (pFin E (((x : UA E n) : GA E n).val i j)) ∈ Formalism.UG.Ov E w := by
    simp only [Filter.eventually_all]; exact fun i j => h _
  have h2 : ∀ᶠ w in cofinite, ∀ i j, pLoc E w (pFin E ((((x : UA E n) : GA E n))⁻¹.val i j)) ∈ Formalism.UG.Ov E w := by
    simp only [Filter.eventually_all]; exact fun i j => h _
  filter_upwards [h1, h2] with w a b
  have hK : cLoc w (x : UA E n) ∈ GlobalTheory.LFun.KGL w (n := n) := by
    refine mem_GLint_of_entries _ _ (fun i j => a i j) (fun i j => ?_)
    rw [← map_inv]
    exact b i j
  unfold toSub
  split_ifs with hU
  · exact Subgroup.mem_subgroupOf.2 hK
  · exact one_mem _

theorem cLoc_finPt_val (w : Pl E) (γ : UE E n) :
    (cLoc w ((finPt γ : finU (E := E) (n := n)) : UA E n)).val = γ.1.val.map (algebraMap E (w.adicCompletion E)) := by
  rw [FinPtLoc.finPt_eq]
  refine Matrix.ext fun i j => ?_
  change pLoc E w (pFin E ((finGL E n (ratF E n γ.1)).val i j)) = algebraMap E _ (γ.1.val i j)
  rw [FinPtLoc.snd_entry]
  rfl

theorem separable_of_monic_natDegree_le_one {K : Type} [Field K] {p : K[X]} (hm : p.Monic) (hd : p.natDegree ≤ 1) :
    p.Separable := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hd with h | h
  · rw [Polynomial.eq_one_of_monic_natDegree_zero hm h]; exact separable_one
  · rw [Polynomial.Monic.eq_X_add_C hm h]; exact separable_X_add_C _

end GlobalTheory.BCT.RegVan

theorem GlobalTheory.BCT.regvan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E))
    (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ), IsTest (KL n) K' f → ∀ w ∈ S,
    (∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) → ∀ (x : finU (E := E) (n := n)) (γ : UE E n),
    globFn S f (x⁻¹ * finPt γ * x) ≠ 0 → γ.1.val.charpoly.Separable := by
  intro E _ _ _ n S K' f hT w hw hsep x γ hne
  set y : finU (E := E) (n := n) := x⁻¹ * finPt γ * x with hy
  set g : Pl E → ℂ := fun u => f u (toSub (UL n u) (cLoc u (y : UA E n))) with hg
  have hev : ∀ᶠ u in cofinite, g u = 1 := by
    filter_upwards [RegVan.eventually_toSub_mem y, hT.2] with u a b
    simp only [hg, b]
    rw [Set.indicator_of_mem a]
    rfl
  have hfin : (Function.mulSupport g).Finite := hev
  have hgw : g w ≠ 0 := by
    intro h0
    apply hne
    unfold globFn
    rw [finprod_mem_def]
    refine finprod_eq_zero (S.mulIndicator g) w (by rw [Set.mulIndicator_of_mem hw]; exact h0) ?_
    exact hfin.subset (by rw [Set.mulSupport_mulIndicator]; exact Set.inter_subset_right)
  have hs := hsep _ hgw
  by_cases hmem : cLoc w (y : UA E n) ∈ UL n w
  · rw [show toSub (UL n w) (cLoc w (y : UA E n)) = ⟨_, hmem⟩ from dif_pos hmem] at hs
    change (cLoc w (y : UA E n)).val.charpoly.Separable at hs
    have hyv : (cLoc w (y : UA E n)).val = (cLoc w (x : UA E n))⁻¹.val *
        (cLoc w ((finPt γ : finU (E := E) (n := n)) : UA E n)).val * (cLoc w (x : UA E n)).val := by
      rw [hy]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, Units.val_mul]
    rw [hyv, Matrix.coe_units_inv, Matrix.charpoly_units_conj', RegVan.cLoc_finPt_val, Matrix.charpoly_map] at hs
    exact (separable_map _).1 hs
  · rw [show toSub (UL n w) (cLoc w (y : UA E n)) = 1 from dif_neg hmem] at hs
    change (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)).charpoly.Separable at hs
    rw [Matrix.charpoly_one, Fintype.card_fin, ← C_1] at hs
    have hn : n ≤ 1 := by
      rcases hs.of_pow' with h | ⟨_, h⟩ | h
      · exact absurd h (not_isUnit_X_sub_C _)
      · omega
      · omega
    exact RegVan.separable_of_monic_natDegree_le_one (Matrix.charpoly_monic _)
      (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; exact hn)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelMeanValueNonnegative
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.OrbFinAf.KottLat

variable {p : ℕ} [Fact p.Prime]

theorem isIntV_add (G : HTGroup p) (v : AwayP p) {a b : Qv v ⊗[ℚ] G.C} (ha : IsIntV G v a)
    (hb : IsIntV G v b) : IsIntV G v (a + b) := fun i => by
  rw [map_add (f := _), Finsupp.add_apply]; exact Subring.add_mem _ (ha i) (hb i)

theorem isIntV_zero (G : HTGroup p) (v : AwayP p) : IsIntV G v 0 := fun i => by
  rw [map_zero, Finsupp.zero_apply]; exact Subring.zero_mem _

theorem eventually_isIntV_map (G : HTGroup p) (y : AfP p ⊗[ℚ] G.C) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
      IsIntV G v (Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C) y) := by
  induction y using TensorProduct.induction_on with
  | zero => exact Filter.Eventually.of_forall fun v => by rw [map_zero]; exact isIntV_zero G v
  | tmul a c =>
    have h1 : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
        AfP.eval v a ∈ v.1.adicCompletionIntegers ℚ := a.2
    have h2 : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ i,
        algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr c i) ∈ v.1.adicCompletionIntegers ℚ := by
      simp only [Filter.eventually_all]; intro i; exact eventually_rat_mem_integers _
    filter_upwards [h1, h2] with v hv1 hv2 i
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsIntV, basV,
      Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
    exact Subring.mul_mem _ hv1 (hv2 i)
  | add y z hy hz =>
    filter_upwards [hy, hz] with v h1 h2
    rw [map_add (f := _)]; exact isIntV_add G v h1 h2

end GlobalTheory.OrbFinAf.KottLat

namespace GlobalTheory.OrbFinAf.KottLat

theorem conj_integral {A K : Type} [Ring A] [CommRing K] {n : ℕ} (R : Subring K)
    (Φ : Matrix (Fin n) (Fin n) K ≃+* A) (hfin : Set.Finite {I : Ideal R | I.IsMaximal})
    (Q : Polynomial R) (hQs : Q.Separable) (γ₀ : Aˣ) (hQm : Q.map R.subtype = (Φ.symm γ₀).charpoly)
    (hγ : ∀ i j, Φ.symm γ₀ i j ∈ R) (g : Aˣ) (hδ : ∀ i j, Φ.symm ((g⁻¹ * γ₀ * g : Aˣ) : A) i j ∈ R) :
    ∃ U : Aˣ, U * (g⁻¹ * γ₀ * g) = γ₀ * U ∧ (∀ i j, Φ.symm (U : A) i j ∈ R) ∧
      (∀ i j, Φ.symm ((U⁻¹ : Aˣ) : A) i j ∈ R) := by
  have lift : ∀ a : A, (∀ i j, Φ.symm a i j ∈ R) →
      ∃ M : Matrix (Fin n) (Fin n) R, M.map R.subtype = Φ.symm a :=
    fun a h => ⟨fun i j => ⟨_, h i j⟩, by ext i j; rfl⟩
  obtain ⟨Γ, hΓ⟩ := lift _ hγ
  obtain ⟨Δ, hΔ⟩ := lift _ hδ
  have hcΓ : Γ.charpoly.map R.subtype = (Φ.symm γ₀).charpoly := by
    rw [← Matrix.charpoly_map, hΓ]
  have hcΔ : Δ.charpoly.map R.subtype = (Φ.symm γ₀).charpoly := by
    rw [← Matrix.charpoly_map, hΔ]
    have e : Φ.symm ((g⁻¹ * γ₀ * g : Aˣ) : A) =
        (((Units.map (Φ.symm : A ≃+* _).toRingHom.toMonoidHom g)⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) :
          Matrix (Fin n) (Fin n) K) * Φ.symm γ₀ *
        ((Units.map (Φ.symm : A ≃+* _).toRingHom.toMonoidHom g : (Matrix (Fin n) (Fin n) K)ˣ) :
          Matrix (Fin n) (Fin n) K) := by
      rw [Units.val_mul, Units.val_mul, map_mul, map_mul]; rfl
    rw [e, Matrix.charpoly_mul_comm, ← mul_assoc, Units.mul_inv, one_mul]
  have hinj : Function.Injective (Polynomial.map R.subtype) :=
    Polynomial.map_injective _ Subtype.val_injective
  have heq : Γ.charpoly = Δ.charpoly := hinj (hcΓ.trans hcΔ.symm)
  have hQ : Q = Γ.charpoly := hinj (hQm.trans hcΓ.symm)
  obtain ⟨u, hu⟩ := GlobalTheory.T.semilocal_conjugate_same_charpoly R hfin n Γ Δ heq (hQ ▸ hQs)
  let F : Matrix (Fin n) (Fin n) R →* A := (Φ.toRingHom.comp R.subtype.mapMatrix).toMonoidHom
  let U : Aˣ := Units.map F u
  have hUs : Φ.symm (U : A) = (u : Matrix (Fin n) (Fin n) R).map R.subtype := Φ.symm_apply_apply _
  have hUs' : Φ.symm ((U⁻¹ : Aˣ) : A) = ((u⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).map R.subtype := by
    rw [show U⁻¹ = Units.map F u⁻¹ from (map_inv (Units.map F) u).symm]
    exact Φ.symm_apply_apply _
  refine ⟨U, Units.ext (Φ.symm.injective ?_), fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul U, Units.val_mul γ₀, map_mul, map_mul, hUs, ← hΔ, ← hΓ, ← Matrix.map_mul,
      ← Matrix.map_mul, hu]
  · rw [hUs, Matrix.map_apply]; exact (u : Matrix (Fin n) (Fin n) R) i j |>.2
  · rw [hUs', Matrix.map_apply]; exact ((u⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j |>.2

end GlobalTheory.OrbFinAf.KottLat

namespace GlobalTheory.OrbFinAf.KottLat

end GlobalTheory.OrbFinAf.KottLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncChartBaseChange
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.LogPair

theorem sncChart_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (C : SncChart f d L σ), IsPullback π f' f (spMap φ) → ∃ C' : SncChart f' d (fun i => (L i).pull π) (fun i => Cartier.secPull (σ i) π), C'.U = π ⁻¹ᵁ C.U := by
  intro R R' _ _ φ X X' f f' π d s L σ C hP
  obtain ⟨hA, hE⟩ := _root_.GlobalTheory.LogPair.isEtCoord_baseChange R R' φ X X' f f' π C.U d C.t hP C.affine C.etale
  refine ⟨{
    U := π ⁻¹ᵁ C.U
    affine := hA
    t := fun a => (π.app C.U).hom (C.t a)
    etale := hE
    c := fun i => fun _ => C.c i
    le := fun i => (π.preimage_mono (C.le i)).trans (Cartier.pull_U (L i) π fun _ => C.c i).ge
    e := C.e
    inj := C.inj
    u := fun i => Units.map (π.app C.U).hom (C.u i)
    eq := fun i => ?_ }, rfl⟩
  show resG X' _ (resG X' _ ((π.app _).hom ((σ i).f (C.c i)))) = _
  rw [Cartier.resG_resG, ← Cartier.app_resG π (C.le i), C.eq i, map_mul]
  rcases h : C.e i with _ | a
  · simp
  · simp
end GlobalTheory.LogPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareZeroLiftingOfNoetherianCase
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

theorem sqLifting_of_noetherian : AbelianDeRham → (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (hI : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I → LiftObj (divided₂ hI) π ∧ LiftHom (divided₂ hI) π) → SqLifting := by
  intro P H R _ I h R₀ _ π hπ hI
  refine ⟨GlobalTheory.T.grothendieckMessing_lift_of_noetherian_case P H R I h R₀ π hπ hI, ?_⟩
  intro g A₀ _ A _ i hA hAa hg g' B₀ _ B _ j hB hBa hg' f₀ _ hf
  obtain ⟨φ, hφ⟩ := _root_.GlobalTheory.liftHom_exists_of_noetherian P H R I h R₀ π hπ hI g A₀ A i hA hAa hg g' B₀ B j hB hBa hg' f₀ hf
  exact _root_.GlobalTheory.HomLift.existsUnique_isMonHom_lift R R₀ π hπ ⟨2, by rw [hI]; exact h⟩ A₀ B₀ A B i j hA hB hAa hBa f₀ φ hφ

end GlobalTheory.SqLift
end

