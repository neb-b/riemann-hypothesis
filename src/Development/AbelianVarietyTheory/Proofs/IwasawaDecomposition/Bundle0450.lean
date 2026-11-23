module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelContainsDeepCongruenceAtBadPrime
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0438
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0213
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1035
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0866
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0865
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockVectorMixedLaplacianKilledLoweringKilled
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0445
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockVectorsKilledHeisenbergAverageIsotropic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0442
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0402

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatSmulMem
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.L2.Forms Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PrincLat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_nat_mul_mem (c : E) : ∃ m : ℕ, 0 < m ∧ (m : E) * c ∈ intOE E := by
  obtain ⟨y, hy, hint'⟩ := exists_integral_multiples ℤ ℚ ({c} : Finset E)
  have hint := hint' c (Finset.mem_singleton_self c)
  have key : ∃ n : ℕ, n ≠ 0 ∧ IsIntegral ℤ ((n : E) * c) := by
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg y
    · refine ⟨n, by rintro rfl; simp at hy, ?_⟩
      have e : ((n : E) * c) = ((n : ℤ) • c) := by rw [zsmul_eq_mul]; push_cast; ring
      rw [e]; exact hint
    · refine ⟨n, by rintro rfl; simp at hy, ?_⟩
      have e : ((n : E) * c) = -((-(n : ℤ)) • c) := by rw [zsmul_eq_mul]; push_cast; ring
      rw [e]; exact hint.neg
  obtain ⟨n, hn, h2⟩ := key
  refine ⟨n, Nat.pos_of_ne_zero hn, ?_⟩
  obtain ⟨a, ha⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).1 h2
  exact ⟨a, ha⟩

theorem exists_nat_smul_mem {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E))
    (hsp : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) (w : Fin r → E) :
    ∃ k : ℕ, 0 < k ∧ (k : E) • w ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.NatMulIntegralExists.main
  | exact _root_.GlobalTheory.NatMulIntegralExists.main
  | (apply _root_.GlobalTheory.NatMulIntegralExists.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMulIntegralExists.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMulIntegralExists.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMulIntegralExists.main ..)

theorem exists_nat_den {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E)) (hfg : Λ.FG) :
    ∃ d : ℕ, 0 < d ∧ ∀ w ∈ Λ, ∀ i, (d : E) * w i ∈ intOE E := by
  classical
  obtain ⟨s, rfl⟩ := hfg
  choose m hm hmem using fun (p : (Fin r → E) × Fin r) => exists_nat_mul_mem (E := E) (p.1 p.2)
  refine ⟨∏ p ∈ s ×ˢ Finset.univ, m p, Finset.prod_pos fun p _ => hm p, ?_⟩
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    intro i
    obtain ⟨k, hk⟩ : m (x, i) ∣ ∏ p ∈ s ×ˢ Finset.univ, m p :=
      Finset.dvd_prod_of_mem _ (Finset.mem_product.2 ⟨hx, Finset.mem_univ _⟩)
    have e : ((∏ p ∈ s ×ˢ Finset.univ, m p : ℕ) : E) * x i = (k : E) * ((m (x, i) : E) * x i) := by
      rw [hk]; push_cast; ring
    rw [e]
    exact mul_mem (natCast_mem _ k) (hmem (x, i))
  | zero => intro i; simp
  | add x y _ _ hx hy =>
    intro i
    rw [Pi.add_apply, mul_add]
    exact add_mem (hx i) (hy i)
  | smul a x _ hx =>
    intro i
    have e : ((∏ p ∈ s ×ˢ Finset.univ, m p : ℕ) : E) * (a • x) i =
        algebraMap (𝓞 E) E a * (((∏ p ∈ s ×ˢ Finset.univ, m p : ℕ) : E) * x i) := by
      rw [Pi.smul_apply, Algebra.smul_def]; ring
    rw [e]
    exact mul_mem ⟨a, rfl⟩ (hx i)

theorem den_locL (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E)) {d : ℕ}
    (hd : ∀ w ∈ Λ, ∀ i, (d : E) * w i ∈ intOE E) {y : Fin r → E ⊗[F] v.adicCompletion F}
    (hy : y ∈ Formalism.L2.Herm.locL v Λ) :
    ∀ i, (d : E ⊗[F] v.adicCompletion F) * y i ∈ intV E v := by
  unfold Formalism.L2.Herm.locL latS at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    intro i
    have e : (d : E ⊗[F] v.adicCompletion F) * inclE (F := F) (v.adicCompletion F) (w i) =
        inclE (F := F) (v.adicCompletion F) ((d : E) * w i) := by
      rw [map_mul, map_natCast]
    rw [e]
    exact Subring.subset_closure (Or.inl ⟨⟨_, hd w hw i⟩, rfl⟩)
  | zero => intro i; simp
  | add x y _ _ hx hy =>
    intro i
    rw [Pi.add_apply, mul_add]
    exact add_mem (hx i) (hy i)
  | smul a x _ hx =>
    intro i
    rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, mul_left_comm]
    exact mul_mem a.2 (hx i)

theorem princ_lat : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {r : ℕ} (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (Fin r → E)), Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → ∃ d : ℕ, 0 < d ∧ ∀ (M : ℕ) (x : Matrix (Fin r) (Fin r) (E ⊗[F] v.adicCompletion F)), (∀ y ∈ Formalism.L2.Herm.locL v Λ, ∃ z ∈ Formalism.L2.Herm.locL v Λ, x *ᵥ y - y = ((M * d : ℕ) : E ⊗[F] v.adicCompletion F) • z) → ∀ a b, ∃ c ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring, (x - 1) a b = (M : E ⊗[F] v.adicCompletion F) * c := by
  intro F E _ _ _ _ _ r v Λ hfg hsp
  classical
  choose k hk hkmem using fun b : Fin r => exists_nat_smul_mem Λ hsp (Pi.single b 1)
  obtain ⟨d₂, hd₂, hden⟩ := exists_nat_den Λ hfg
  have hd₁ : 0 < ∏ b, k b := Finset.prod_pos fun b _ => hk b
  have hmem : ∀ b, ((∏ b, k b : ℕ) : E) • (Pi.single b 1 : Fin r → E) ∈ Λ := fun b => by
    obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem k (Finset.mem_univ b)
    have e : ((∏ b, k b : ℕ) : E) • (Pi.single b 1 : Fin r → E) = t • ((k b : E) • (Pi.single b 1 : Fin r → E)) := by
      rw [← Nat.cast_smul_eq_nsmul E, smul_smul, ht, Nat.cast_mul, mul_comm]
    rw [e]
    exact Λ.toAddSubmonoid.nsmul_mem (hkmem b) t
  refine ⟨(∏ b, k b) * d₂, Nat.mul_pos hd₁ hd₂, fun M x hx a b => ?_⟩
  set d₁ := ∏ b, k b with hd₁def
  let y : Fin r → E ⊗[F] v.adicCompletion F :=
    fun i => inclE (F := F) (v.adicCompletion F) (((d₁ : E) • (Pi.single b 1 : Fin r → E)) i)
  have hy : y ∈ Formalism.L2.Herm.locL v Λ := Submodule.subset_span ⟨_, hmem b, rfl⟩
  obtain ⟨z, hz, hxz⟩ := hx y hy
  have hy' : y = (d₁ : E ⊗[F] v.adicCompletion F) • (Pi.single b 1 : Fin r → E ⊗[F] v.adicCompletion F) := by
    funext i
    simp only [y, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast]
    by_cases h : i = b
    · subst h; simp
    · simp [Pi.single_apply, h]
  have hcol : x *ᵥ y - y = (d₁ : E ⊗[F] v.adicCompletion F) • ((x - 1) *ᵥ Pi.single b 1) := by
    rw [hy', Matrix.mulVec_smul, Matrix.sub_mulVec, Matrix.one_mulVec, smul_sub]
  have h1 := congrFun hxz a
  rw [hcol, Pi.smul_apply, Pi.smul_apply, Matrix.mulVec_single_one, Matrix.col_apply, smul_eq_mul,
    smul_eq_mul] at h1
  have hu : IsUnit (d₁ : E ⊗[F] v.adicCompletion F) := by
    have := (IsUnit.mk0 (d₁ : F) (Nat.cast_ne_zero.2 hd₁.ne')).map (algebraMap F (E ⊗[F] v.adicCompletion F))
    rwa [map_natCast] at this
  refine ⟨(d₂ : E ⊗[F] v.adicCompletion F) * z a, den_locL v Λ hden hz a, ?_⟩
  apply hu.mul_left_cancel
  rw [h1]
  push_cast
  ring

end GlobalTheory.PrincLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRationalFramesNearAdelicAtBadPrimes
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.AdT.Approx

open scoped TensorProduct

variable {F E : Type} {_iF : Field F} [NumberField F] {_iE : Field E} [NumberField E] {_iA : Algebra F E} {n : ℕ}

theorem comp_mul_rat (P : HeightOneSpectrum (𝓞 E)) (k : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) E) :
    ((k⁻¹ * GlobalTheory.TwU.ratA F γ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) _).map (adAt F P) =
      ((Formalism.UG.bc (adAt F P) k)⁻¹ : GL (Fin n) (P.adicCompletion E)).1 * γ.1.map (algebraMap E (P.adicCompletion E)) := by
  rw [← map_inv, Units.val_mul, Matrix.map_mul]
  congr 1
  show (γ.1.map (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F))).map (adAt F P) = _
  rw [Matrix.map_map]
  congr 1
  funext x
  exact adAt_inclE F P x

theorem comp_rat_mul (P : HeightOneSpectrum (𝓞 E)) (k : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) E) :
    (((GlobalTheory.TwU.ratA F γ)⁻¹ * k : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) _).map (adAt F P) =
      (γ⁻¹).1.map (algebraMap E (P.adicCompletion E)) * (Formalism.UG.bc (adAt F P) k : GL (Fin n) (P.adicCompletion E)).1 := by
  rw [← map_inv, Units.val_mul, Matrix.map_mul]
  congr 1
  show ((γ⁻¹).1.map (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F))).map (adAt F P) = _
  rw [Matrix.map_map]
  congr 1
  funext x
  exact adAt_inclE F P x

end GlobalTheory.Mem.Col2.AdT.Approx

namespace GlobalTheory.Mem.Col2.AdT

theorem frNear_exists : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (n : ℕ) (k : GL (Fin n) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)), ∃ fb : SBof I a → GL (Fin n) (I.rec7 l Z).host.E, FrNear I l Z a k fb := by
  intro B X I hOk l Z a n k
  have key : ∀ P : SBof I a, ∃ γ : GL (Fin n) (I.rec7 l Z).host.E,
      GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) (k⁻¹ * GlobalTheory.TwU.ratA (I.rec7 l Z).host.F γ) ∧
      GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) ((GlobalTheory.TwU.ratA (I.rec7 l Z).host.F γ)⁻¹ * k) := by
    intro P
    obtain ⟨γ, hγ⟩ := _root_.GlobalTheory.DenseGL.dense_two_sided B.fields.E P.1 n ((I.cst a).D P) (Formalism.UG.bc (adAt B.host.F P.1) k)
    refine ⟨γ, ?_, ?_⟩
    · rw [(_root_.GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary.main I hOk l Z a n ((I.cst a).D P) P _).2.2]
      intro r s
      have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) _ => M r s) (Approx.comp_mul_rat P.1 k γ)
      simp only [Matrix.map_apply] at h1
      have h2 := (hγ r s).1
      rw [Matrix.sub_apply] at h2
      convert h2 using 3
      exact h1
    · rw [(_root_.GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary.main I hOk l Z a n ((I.cst a).D P) P _).2.2]
      intro r s
      have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) _ => M r s) (Approx.comp_rat_mul P.1 k γ)
      simp only [Matrix.map_apply] at h1
      have h2 := (hγ r s).2
      rw [Matrix.sub_apply] at h2
      convert h2 using 3
      exact h1
  choose fb hfb using key
  exact ⟨fb, hfb⟩

end GlobalTheory.Mem.Col2.AdT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaLiftLinearMapCuspFormMultiplicity
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.DefLift.ThetaMap

open GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions

variable {D : D7}


open Classical in
theorem restrictsTo_of_eq {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} (h1 : LowSm M)
    (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T)
    {U : KMap M} (hU : KEquiv θ M U) (e : ∀ τ, lowT M τ) (he : ∀ τ, e τ ≠ 0)
    (h : T (fun τ => (e τ : M.sm τ)) = U e) : RestrictsTo M T U := by
  intro v
  have key := mem_of_translates h1 h2 (T.compLinearMap (fun τ => (lowT M τ).subtype) - U) ⊥ e he
    (by simpa [sub_eq_zero] using h) (fun τ k hk v u hu hv => ?_) v
  · simpa [sub_eq_zero] using key
  · have hv' : T (fun τ => (v τ : M.sm τ)) = U v := by simpa [sub_eq_zero] using hv
    have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
    have hg : (M.fr τ)⁻¹ * k * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
      have hk' : kᴴ * Formalism.REAL.Jm (M.ε τ) * k = Formalism.REAL.Jm (M.ε τ) := kset_uj hk
      have e1 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by
        rw [← conjTranspose_mul, mul_nonsing_inv _ hd, conjTranspose_one]
      change ((M.fr τ)⁻¹ * k * M.fr τ)ᴴ * gramAt D V τ * ((M.fr τ)⁻¹ * k * M.fr τ) = gramAt D V τ
      calc ((M.fr τ)⁻¹ * k * M.fr τ)ᴴ * gramAt D V τ * ((M.fr τ)⁻¹ * k * M.fr τ)
          = (M.fr τ)ᴴ * (kᴴ * (((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ) * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * k) *
              M.fr τ := by
            rw [← M.fr_gram τ]; simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = gramAt D V τ := by rw [e1, mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.mul_one, hk', M.fr_gram]
    have e2 : M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ = k := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_assoc,
        mul_nonsing_inv _ hd, Matrix.mul_one]
    have e3 := hT.equiv τ _ hg (fun τ => (v τ : M.sm τ)) (u : M.sm τ) (by
      rw [hu, DSModel.rep, e2])
    have e4 : (fun ρ => ((Function.update v τ u ρ : lowT M ρ) : M.sm ρ)) =
        Function.update (fun ρ => (v ρ : M.sm ρ)) τ (u : M.sm τ) :=
      funext fun ρ => Function.apply_update (fun ρ (y : lowT M ρ) => (y : M.sm ρ)) v τ u ρ
    have e5 : T (fun ρ => ((Function.update v τ u ρ : lowT M ρ) : M.sm ρ)) = U (Function.update v τ u) := by
      rw [e4, e3, hv', hU τ k hk v u hu]
    simpa [sub_eq_zero] using e5

theorem exists_extension (hP : GlobalTheory.Published.CuspRapidDecay) {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D}
    {S : D.what₂.Tau → SPar} {M : DSModel V S} (hM : HolShape M) {w : D.what₂.Tau → Fin V.rank → ℤ} (hw : WtIs M w)
    {J : Set (GA D V)} (hJ : J ⊆ (GfC V : Set (GA D V))) {χ : GA D V → ℂ} {U : KMap M} (ha : ∀ e, IsAutFun V (U e))
    (hl : ∀ e, ∀ k ∈ J, ∀ g, U e (g * k) = χ k * U e g) (hs : ∀ e, IsSmoothFn V θ (U e))
    (hg : ∀ e, IsUnifModGrowth V θ (U e)) (hz : ∀ e, ZCusp V (U e)) (hk : KEquiv θ M U)
    (hh : ∀ τ, ∀ Z ∈ pMinus M τ, ∀ e, RderC θ V τ Z (U e) = 0) :
    ∃ T : MMap M, IsMultMap θ M J χ T ∧ RestrictsTo M T U := by
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.HolLowOnce.lowSm_and_lowIrr D V S M hM
  obtain ⟨v, hv⟩ := exists_isExtVec M h1
  let e : ∀ τ, lowT M τ := fun τ => ⟨v τ, (hv τ).2.1⟩
  have he : ∀ τ, e τ ≠ 0 := fun τ h0 => by
    have h3 : v τ = 0 := congrArg Subtype.val h0
    have := (hv τ).1
    rw [h3] at this
    simp at this
  have hfin : ∃ μ 𝓕, FinPair V μ 𝓕 := by
    obtain ⟨_, _, _, _⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V
    have : IsTopologicalGroup (GA D V) :=
      inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
    have hμ : (Measure.haar : Measure (GA D V)).IsHaarMeasure := inferInstance
    obtain ⟨hr, 𝓕, h𝓕⟩ := GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V _ hμ
    exact ⟨_, 𝓕, hμ, hr, h𝓕, (GlobalTheory.Mem.QuotVol.quot_volume_ne_zero_ne_top D V _ 𝓕 ⟨hμ, h𝓕⟩).2⟩
  obtain ⟨T, hT, hTe⟩ := GlobalTheory.T.boundedHolomorphicForm_eq_multiplicitySpace_value D θ V S M w v hθ hM hw hv hfin J χ (U e) hJ
    ⟨ha e, _root_.GlobalTheory.CuspDecay.bounded_of_smooth_unifModGrowth hP D θ V hθ _ (ha e) (hs e) (hg e) (_root_.GlobalTheory.TransvCusp.isCuspFun_of_zCusp D θ V hθ _ (ha e) (hz e)), hl e,
      _root_.GlobalTheory.KMapHol.holAd_of_kEquiv D θ V S M w hθ hM hw h1 h2 U hs hk hh e hv⟩ (hz e)
  exact ⟨T, hT, restrictsTo_of_eq h1 h2 hT hk e he hTe⟩


open Classical in
theorem exists_member (hP : GlobalTheory.Published.CuspRapidDecay) {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
    {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om)
    {θ : InfFam D} (hθ : IsInfFam θ) (hpos : ∀ τ, (gramAt D S τ).PosDef)
    {Sp : D.what₂.Tau → SPar} {M : DSModel T Sp} (hM : HolShape M) {w : D.what₂.Tau → Fin T.rank → ℤ} (hw : WtIs M w)
    {c : CoefA S} (hc : c.Is) (pt : PolF D T.rank S.rank →ₗ[ℂ] (WO S T → ℂ)) (hpt : ∀ P, IsThetaFunO ψ S T (pt P))
    {Δ : PolF D T.rank S.rank} {io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D T.rank S.rank}
    (hio : IsIoW θ M c om (fun P => pt P) Δ io)
    (hΔ : ∀ τ, ∀ Z ∈ pMinus M τ, ∀ h, RderC θ T τ Z (fun g => thetaKO om h g (pt Δ)) = 0)
    {J : Set (GA D T)} (hJ : J ⊆ (GfC T : Set (GA D T)))
    (hJo : ∃ U : Subgroup (GA D T), IsOpen (U : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC T → k ∈ J)
    (hfix : ∀ k ∈ J, ∀ P, om (1, k) (pt P) = pt P) {χ : GA D T → ℂ} (hχ : ∀ k, χ k = 1)
    (hsupp : ∀ P h g ξ, IsoVec T ξ → ∃ n : ℕ, 0 < n ∧ ∃ a : Fin n → Fin S.rank → AE D,
      ∑ k, heisO ψ S T (along S T ξ (a k)) (om (h, g) (pt P)) = 0)
    {F : GA D S → c.W} (hF : Continuous F) (hFi : ∀ γ ∈ GQ S, ∀ h, F (γ * h) = F h)
    {ν : Measure (GA D S)} {𝓕 : Set (GA D S)} (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ S) 𝓕 ν) :
    ∃ Θ : MMap M, IsMultMap θ M J χ Θ ∧ ∀ v : ∀ ρ, lowT M ρ,
      Θ (fun ρ => (v ρ : M.sm ρ)) = lift om ν 𝓕 fun h => pt (io (PiTensorProduct.tprod ℂ v) (F h)) := by
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.HolLowOnce.lowSm_and_lowIrr D T Sp M hM
  have hint : ∀ e g, IntegrableOn (fun h => thetaKO om h g (pt (io e (F h)))) 𝓕 ν := fun e g =>
    GlobalTheory.DefiniteQuotient.integrableOn_theta D ψ hom.std S T χS χT om hom hpos c.W (pt ∘ₗ io e)
      (fun _ => hpt _) _ hF hFi ν 𝓕 hν h𝓕 g
  let U₀ : LowT M →ₗ[ℂ] (GA D T → ℂ) :=
    { toFun := fun e => lift om ν 𝓕 fun h => pt (io e (F h))
      map_add' := fun e e' => by
        funext g
        simp only [lift, thetaKO, map_add (f := _), LinearMap.add_apply, Pi.add_apply]
        exact integral_add (hint e g) (hint e' g)
      map_smul' := fun a e => by
        funext g
        simp only [lift, thetaKO, map_smul, LinearMap.smul_apply, Pi.smul_apply, RingHom.id_apply]
        exact integral_smul a _ }
  let U : KMap M := U₀.compMultilinearMap (PiTensorProduct.tprod ℂ)
  have hU : ∀ v, U v = lift om ν 𝓕 fun h => (pt ∘ₗ io (PiTensorProduct.tprod ℂ v)) (F h) := fun _ => rfl
  have hmul : ∀ h g k φ, thetaKO om h (g * k) φ = thetaKO om h g (om (1, k) φ) := fun h g k φ => by
    unfold thetaKO
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have hlev : ∀ v, ∀ k ∈ J, ∀ g, U v (g * k) = U v g := fun v k hk g => by
    simp only [hU, lift, hmul, LinearMap.comp_apply, hfix k hk]
  have hd := fun v => _root_.GlobalTheory.DefLiftDer.lift_continuous_invariant_hasDerivAt D ψ S T χS χT om hom θ hθ hpos c.W (pt ∘ₗ io (PiTensorProduct.tprod ℂ v))
    (fun _ => hpt _) F hF hFi ν 𝓕 hν h𝓕
  have hs := fun v => _root_.GlobalTheory.DefLiftSmooth.lift_smooth_growth_killed D ψ S T χS χT om hom θ hθ hpos c.W (pt ∘ₗ io (PiTensorProduct.tprod ℂ v))
    (fun _ => hpt _) F hF hFi ν 𝓕 hν h𝓕
  have hz := fun v => _root_.GlobalTheory.DefLiftCusp.zcusp_lift D ψ S T χS χT om hom hpos c.W (pt ∘ₗ io (PiTensorProduct.tprod ℂ v))
    (fun _ => hpt _) F hF hFi ν 𝓕 hν h𝓕 fun x h g ξ hξ => hsupp _ h g ξ hξ
  obtain ⟨O, hO, hOJ⟩ := hJo
  exact exists_extension hP hθ hM hw hJ (U := U)
    (fun v => ⟨(hd v).1.2, ⟨O, hO, fun k hk hk' => hlev v k (hOJ k hk hk')⟩, (hd v).1.1⟩)
    (fun v k hk g => by rw [hχ, one_mul, hlev v k hk]) (fun v => (hs v).1) (fun v => (hs v).2.1) hz
    (fun τ k hk v u hu => by
      funext g
      simp only [hU, lift, rTr, hmul, LinearMap.comp_apply, hio.2.1 τ k hk v u hu])
    fun τ Z hZ v => (hs v).2.2 τ Z fun x h =>
      _root_.GlobalTheory.DefLift.LowerKill.values_killed D ψ S T χS χT om hom θ hθ Sp M h1 h2 c hc pt hpt Δ io hio hΔ τ Z hZ v x h

theorem level_open (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → k ∈ levS V β L := by
  classical
  have : IsTopologicalGroup (GA D V) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  refine ⟨(lev D.sp.cm V.gram β L).comap (Lev.finE V), Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_, fun k hk hk' => ⟨hk', hk⟩⟩
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ V β (L.Pg ∪ L.Q)] with κ hh
  obtain ⟨h1, h2, h3⟩ := hh
  exact Kg_le_lev (D := L) (T := L.Pg ∪ L.Q) Finset.subset_union_left Finset.subset_union_right
      ⟨⟨h1, h2⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_princAt.2 ⟨h2, h3 PP hP⟩⟩

theorem pureTensorO_one {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} sS sT BS BT (f : WO S T → ℂ) :
    pureTensorO ψ θ S T sS sT BS BT f 1 = f := by
  have : (1 : PolF D T.rank S.rank) = MvPolynomial.basisMonomials _ ℂ 0 := by simp
  rw [this, pureTensorO, pureTensorL, Module.Basis.constr_basis]
  simp [opPow]

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem firesAt (hP : GlobalTheory.Published.CuspRapidDecay) (R : RealDat D A Ks) (h0 : R.toLevCh.Is A.μ0) (hm : R.IsModels)
    (hω : R.thP_ωP) (hv : R.thP_vP) (hp : R.thP_pt_theta) (hio : R.thP_ioP) (i : Fin D.R.m) (t : T) (x : (R.HV i t).H) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelFiring.FiresAt R i t x := by
  have hx : (R.HV i t).e x ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ
      (levEnv _ (R.βV i) (R.datVt i t)).J (levEnv _ (R.βV i) (R.datVt i t)).χ :=
    (hm.HV i t).2.1.le (LinearMap.mem_range_self _ x)
  have hpos : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ => by
    have := D.sp.V_sig ((i : ℕ) + 1) (tauE D τ)
    rw [hm.vpos i] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  have hth : ∀ i t, IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := fun i t => by
    have := hp i t 1
    rwa [RealDat.ptP, pureTensorO_one] at this
  obtain ⟨hM, w, hw⟩ := _root_.GlobalTheory.DefLift.holShape_fixed D G Pl0 T A Ks R hm.order i
  have hpq : ∀ τ, ((Wc D i).sig (tauE D τ)).1 + ((Wc D i).sig (tauE D τ)).2 ≤ (Vc D i).rank := fun τ => by
    have e := GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW_add_qW i τ
    have e' := rank_Wc i
    have := r_le_V i
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW, GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.qW] at e
    omega
  have hΔ := fun τ => _root_.GlobalTheory.FockKill.rderC_theta_eq_zero D R.ψ (Vc D i) (Wc D i) _ _ (R.ωP i t) (hω i t) R.θ hm.inf (D.sp.V_sig _) (D.sp.W_sig _)
    (R.BV i) (hm.BV i) _ (R.MW i (sg0 D A)) (fun τ => ((Wc D i).sig (tauE D τ)).1) (hm.order i) (R.vP i t) (hth i t)
    (GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hv i t) (hth i t)) (RealDat.Delta i) τ
    (_root_.GlobalTheory.MinorHarmonic.laplacian_delta D _ _ _ _ _ _ hpq τ)
  have key := exists_member hP (hω i t) hm.inf hpos hM hw (hm.cV i)
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
      (R.vP i t)) (hp i t) (hio i t) hΔ (J := levS _ (R.βW i) (R.datWp i R.triv)) (fun _ hk => hk.1)
    (level_open _ _ _) (fun k hk P => by
      rw [GlobalTheory.OrientedHeis.om_fin_pureTensorO R.ψ _ _ _ _ _ (hω i t) R.θ hm.inf 1 (one_mem _) k hk.1 _ _ _ _ _ P (hth i t),
        _root_.GlobalTheory.DefLift.Level.om_level_vP D G Pl0 T A Ks R h0 hω hv hth i t k hk])
    (GlobalTheory.IndefiniteRowSideFullHecke.VectorLevelCharacters.principalLevelCharacter_eq_one R i) (_root_.GlobalTheory.ThetaSupport.sum_heisO_along_eq_zero D G Pl0 T A Ks R h0 hm.inf hω hv hp i t)
    (GlobalTheory.ThetaIntegrand.ext_continuous (R.cV i) (hm.cV i) _ _ hx) (GlobalTheory.ThetaIntegrand.ext_invariant (R.cV i) hx)
    (hm.νV i t).1.1 (hm.νV i t).2
  obtain ⟨Θ, hΘ, hΘv⟩ := key
  refine ⟨fun e g => ?_, Θ, Submodule.subset_span hΘ, hΘv⟩
  exact GlobalTheory.ThetaIntegrand.integrableOn_form (hω i t) (D.sp.V_sig _) (hm.vpos i) (R.cV i) (hm.cV i) (R.βV i)
    (R.datVt i t) hx
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
      (R.vP i t)) (hp i t) (R.ioP i e) (hm.νV i t) g

theorem exists_thetaMap : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.thP_ωP → R.thP_vP → R.thP_pt_theta → R.thP_ioP → ∃ th, ({ R with thF := th } : RealDat D A Ks).thP_thF_mem ∧ ({ R with thF := th } : RealDat D A Ks).thP_thF := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R h0 _ hm hω hv hp hio
  choose th hth using fun i t =>
    GlobalTheory.ThetaFiresOfMult.exists_isThetaMult_of_firesAt (firesAt hP R h0 hm hω hv hp hio i t)
  exact ⟨th, fun i t => (hth i t).1, fun i t => (hth i t).2⟩

end GlobalTheory.DefLift.ThetaMap

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteAdeleFieldIdentificationEqBaseChangeRingEqStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdeleFieldIdentification_eq_baseChangeRingEquiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ι : AfE F E ≃+* FiniteAdeleRing (𝓞 E) E), GlobalTheory.TwU.IsAdIso ι → ∀ x, ι x = afIso F E x := by
  first | exact @GlobalTheory.isAdIso_eq_afIso | exact GlobalTheory.isAdIso_eq_afIso | (intros; apply GlobalTheory.isAdIso_eq_afIso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsUIff
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.Bl

abbrev DatP : Type 1 := ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok)
  (Wt : Set B.places.Pl), R3.Dat (w.st Z) w.I hX T Wt → Prop

def AtDat (P : DatP) : Prop :=
  StepW Pinned fun K B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : R3.Dat (w.st Z) w.I hX T Wt),
    GrpTrue Z.N f → R3.GrpAt (w.st Z) w.I → z.R.toRealDat.ExAt → GlobalTheory.RealGeo.InGeo z.geo → P K B f T w Z hX Wt z

end GlobalTheory.Mem.Top.Bl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMemPlaceIdealSpanOfNeOneStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_mem_placeIdealSpan_of_ne_one : ∀ (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k), ¬ GlobalTheory.Mem.SymFrame.EwAt X (D.naut.plGw kv.1 kv.2) → X.ew ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  first | exact @GlobalTheory.Mem.SymChar.EwZero.ew_mem_wInt | exact GlobalTheory.Mem.SymChar.EwZero.ew_mem_wInt | (intros; apply GlobalTheory.Mem.SymChar.EwZero.ew_mem_wInt <;> assumption)
end

